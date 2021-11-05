(uiop:define-package :immutable-vector/immutable-vector
  (:nicknames :immutable-vector)
  (:import-from :alexandria
                #:array-index #:array-length)
  (:use :cl :iterate)
  (:local-nicknames (:g :generator))
  (:export
   #:immutable-vector
   #:make-vec
   #:vecref #:vec-length
   #:push-back
   #:generate-immutable-vector))
(in-package :immutable-vector/immutable-vector)

(eval-when (:compile-toplevel :load-toplevel)
  (defconstant +vec-branch-rate+ 16)
  (defconstant +max-depth+ (1- (floor (log array-dimension-limit +vec-branch-rate+)))))

(deftype depth ()
  `(integer 0 ,+max-depth+))

(deftype chunk ()
  `(simple-vector ,+vec-branch-rate+))

(declaim (ftype (function ((g:generator t &optional)) (values chunk &optional))
                alloc-chunk))
(defun alloc-chunk (contents-iterator
                    &aux (contents (g:concatenate contents-iterator (g:always '#:uninit))))
  (let* ((arr (make-array +vec-branch-rate+)))
    (iter (declare (declare-variables))
      (for (the fixnum i) below +vec-branch-rate+)
      (setf (svref arr i) (g:next contents)))
    arr))

(deftype one-index ()
  `(integer 0 (,+vec-branch-rate+)))

(deftype tail-buf ()
  (cons 'or
        (iter (declare (declare-variables))
          (for (the fixnum i) to +vec-branch-rate+)
          (collect `(simple-vector ,i)))))

(declaim (type (simple-vector 0) +empty-tail+))
(defparameter +empty-tail+ (vector))

(defstruct (immutable-vector
            (:constructor %make-vec)
            (:copier nil)
            (:conc-name %vec-))
  "An immutable vector backed by a `+vec-branch-rate+'-trie, with a separate tail buffer to make push-back fast."
  (depth (error "supply :depth to %make-vec")
   :type depth)
  (length (error "supply :length to %make-vec")
   :type array-length)
  (body (error "supply :body to %make-vec")
   ;; a trie of `+vec-branch-rate+'-element chunks. restrictions:
   ;; - all leaves are at the same depth, DEPTH
   ;; - no leaf is partially full; every leaf holds exactly `+vec-branch-rate+' elements.
   :type chunk)
  (tail +empty-tail+
   :type tail-buf))

(declaim (ftype (function (immutable-vector) (values array-index &optional))
                tail-length body-length vec-length))
(defun tail-length (vec &aux (tail (%vec-tail vec)))
  (if tail (length tail) 0))
(defun body-length (vec)
  (- (%vec-length vec)
     (tail-length vec)))
(defun vec-length (vec)
  (%vec-length vec))

(declaim (ftype (function (immutable-vector array-index) (values boolean &optional))
                index-in-tail-p))
(defun index-in-tail-p (vec idx)
  "True if IDX is within the tail part of VEC, nil otherwise.

Does not necessarily imply that IDX is in-bounds for VEC."
  (>= idx (body-length vec)))

(declaim (ftype (function (immutable-vector array-index) (values t &optional))
                tailref))
(defun tailref (vec idx)
  "aref into the tail of VEC. IDX must be in-bounds for VEC, and must be `index-in-tail-p'"
  (svref (%vec-tail vec) (- idx (body-length vec))))

(declaim (ftype (function (depth array-index) (values one-index array-index &optional))
                depth-index)
         (inline depth-index))
(defun depth-index (depth index)
  (let ((depth-low-bit (* depth 4)))
    (values (ldb (byte 4 depth-low-bit)
                 index)
            (ldb (byte depth-low-bit 0)
                 index))))

(declaim (ftype (function (chunk depth array-index) (values t &optional))
                trieref))
(defun trieref (body depth idx)
  (if (zerop depth)
      (svref body idx)
      (multiple-value-bind (curr remaining) (depth-index depth idx)
        (trieref (svref body curr) (1- depth) remaining))))

(declaim (ftype (function (t chunk depth array-index) (values t &optional))
                (setf trieref)))
(defun (setf trieref) (new-elt body depth idx)
  (if (zerop depth)
      (setf (svref body idx) new-elt)
      (multiple-value-bind (curr remaining) (depth-index depth idx)
        (setf (trieref (svref body curr) (1- depth) remaining)
              new-elt))))

(declaim (ftype (function (immutable-vector array-index) (values t &optional))
                bodyref))
(defun bodyref (vec idx)
  "aref into the body part of VEC. IDX must be in-bounds for vec, and must not be `index-in-tail-p'."
  (trieref (%vec-body vec) (%vec-depth vec) idx))

(define-condition out-of-bounds ()
  ((%vector :type immutable-vector
            :initarg :vector
            :reader out-of-bounds-vector)
   (%index :type array-index
           :initarg :index
           :reader out-of-bounds-index)))

(defmethod print-object ((err out-of-bounds) stream)
  (if (or *print-escape* *print-readably*) (call-next-method)
      (with-accessors ((vector out-of-bounds-vector)
                       (index out-of-bounds-index))
          err
        (format stream "Invalid index ~d (~@x) for vector of length ~d (~@x): ~a"
                index index (%vec-length vector) (%vec-length vector) vector))))

(declaim (ftype (function (immutable-vector array-index) (values t &optional))
                vecref))
(defun vecref (vec idx)
  (cond ((>= idx (%vec-length vec))
         (error 'out-of-bounds
                :vector vec
                :index idx))
        ((index-in-tail-p vec idx) (tailref vec idx))
        (t (bodyref vec idx))))

(declaim (ftype (function (array-index) (values depth &optional))
                length-required-depth))
(defun length-required-depth (length)
  (case length
    ((0 1) 0)
    (t (values (floor (log (1- length) 16))))))

(declaim (ftype (function (depth) (values array-index &optional))
                elts-per-chunk))
(defun elts-per-chunk (depth)
  (expt +vec-branch-rate+ (1+ depth)))

(declaim (ftype (function (array-index depth)
                          (values array-index &optional))
                length-in-chunks-at-depth))
(defun length-in-chunks-at-depth (total-length depth)
  (values (ceiling total-length (elts-per-chunk depth))))

(declaim (ftype (function (fixnum fixnum fixnum) (values fixnum &optional))
                bracket))
(defun bracket (min middle max)
  (min max (max middle min)))

(declaim (ftype (function (depth array-index (g:generator t &rest t))
                          (values chunk &optional))
                alloc-trie))

(declaim (ftype (function (depth array-index (g:generator t &optional))
                          (values (g:generator chunk &optional) &optional))

                chunks-generator))
(defun chunks-generator (child-depth length-in-elts elements)
  (g:take (g:generator ((per-child-length (elts-per-chunk child-depth))
                        (remaining length-in-elts))
            (declare (type array-index per-child-length)
                     (fixnum remaining))
            (let ((this-length (bracket 0 per-child-length remaining)))
              (declare (type array-index this-length))
              (if (zerop this-length) (g:done)
                  (progn (decf remaining per-child-length)
                         (alloc-trie child-depth this-length elements)))))
          (length-in-chunks-at-depth length-in-elts child-depth)))

(defun alloc-trie (depth length contents)
  (assert (<= 0 length (expt +vec-branch-rate+ (1+ depth))))
  (if (zerop depth)
      (alloc-chunk contents)
      (alloc-chunk (chunks-generator (1- depth) length contents))))

(declaim (ftype (function (immutable-vector) (values (g:generator t &optional) &optional))
                generate-immutable-vector))
(defun generate-immutable-vector (vec)
  "Generate successive elements from the `immutable-vector' VEC"
  (let* ((current-index -1))
    (declare (type (or array-index (eql -1)) current-index))
    (labels ((inbounds-advance ()
               (incf current-index)
               (vecref vec current-index))
             (vec-iter ()
               (if (>= current-index (1- (%vec-length vec)))
                   (g:done)
                   (inbounds-advance))))
      #'vec-iter)))

(defmethod print-object ((vec immutable-vector) stream)
  (write-string "#[" stream)
  (g:do-generator (elt (generate-immutable-vector vec))
    (write-char #\space stream)
    (write elt :stream stream))
  (write-string "]" stream))

(defmethod g:make-generator ((vec immutable-vector))
  (generate-immutable-vector vec))

(declaim (ftype (function (array-length) (values array-length &optional))
                length-without-partial-chunks))
(defun length-without-partial-chunks (total-length)
  (* +vec-branch-rate+ (floor total-length +vec-branch-rate+)))

(declaim (ftype (function (one-index (g:generator t &rest t))
                          (values tail-buf &optional))
                make-tail))
(defun make-tail (length contents)
  (let* ((tail (make-array length)))
    (g:do-generator ((idx elt &rest ignore) (g:enumerate contents) tail)
      (declare (ignore ignore))
      (setf (aref tail idx) elt))))

(declaim (ftype (function (array-length (g:generator t &rest t))
                          (values immutable-vector &optional))
                make-vec))
(defun make-vec (length contents)
  (let* ((body-length (length-without-partial-chunks length))
         (tail-length (- length body-length))
         (depth (length-required-depth body-length)))
    (%make-vec :depth depth
               :length length
               :body (alloc-trie depth body-length contents)
               :tail (make-tail tail-length contents))))

(declaim (ftype (function (immutable-vector &key (:depth depth)
                                            (:length array-length)
                                            (:body chunk)
                                            (:tail tail-buf))
                          (values immutable-vector &optional))
                copy-vec))
(defun copy-vec (vec &key (depth (%vec-depth vec))
                       (length (%vec-length vec))
                       (body (%vec-body vec))
                       (tail (%vec-tail vec)))
  (%make-vec :depth depth
             :length length
             :body body
             :tail tail))

(declaim (ftype (function (tail-buf) (values boolean &optional))
                tail-has-room-p))
(defun tail-has-room-p (tail)
  (< (length tail)
     +vec-branch-rate+))

(declaim (ftype (function (t simple-vector) (values simple-vector &optional))
                vector-push-back))
(defun vector-push-back (new-element vec
                         &aux (new (make-array (1+ (length vec)))))
  (iter (declare (declare-variables))
    (for elt in-vector vec with-index i)
    (setf (svref new i) elt))
  (setf (svref new (length vec)) new-element)
  new)

(declaim (ftype (function (depth) (values array-length &optional))
                max-length-at-depth))
(defun max-length-at-depth (depth)
  (expt +vec-branch-rate+ (1+ depth)))

(declaim (ftype (function (depth chunk) (values chunk &optional))
                wrap-in-spine))
(defun wrap-in-spine (depth body)
  (if (zerop depth) body
      (alloc-chunk (g:generate-list (list body)))))

(declaim (ftype (function (t immutable-vector) (values immutable-vector &optional))
                push-back))
(defun push-back (new-element vec)
  (with-accessors ((depth %vec-depth)
                   (tail %vec-tail)
                   (body %vec-body))
      vec
    (cond ((tail-has-room-p tail)
           ;; fast path when your tail is short: make it longer
           (copy-vec vec :tail (vector-push-back new-element tail)))
          ((= (body-length vec) (max-length-at-depth depth))
           ;; fast path when your tail and body are both full: grow an extra layer of depth, put your old tail
           ;; in the newly-expanded body, then grow a new tail
           (copy-vec vec
                     :depth (1+ depth)
                     :body (alloc-chunk (g:generate-these body
                                                          (wrap-in-spine depth tail)))
                     :tail (vector new-element)))
          ((error "unimplemented")
           ;; slow path: move your full tail into your not-full body, trying your best to preserve as much
           ;; structure as possible, then grow a new tail.
           ))))
