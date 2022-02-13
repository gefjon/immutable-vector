(uiop:define-package :immutable-vector/immutable-vector
  (:nicknames :immutable-vector)
  (:import-from :alexandria
                #:array-index #:array-length #:define-constant #:when-let)
  (:use :cl :iterate)
  (:local-nicknames (:g :generator)
                    (:nr :named-readtables))
  (:export
   #:immutable-vector
   #:make-vec
   #:vecref #:vec-length
   #:push-back
   #:generate-immutable-vector
   #:list-vec #:vector-vec
   #:vec-list #:vec-vector

   #:immutable-vector-readtable))
(in-package :immutable-vector/immutable-vector)

;;; defs

(eval-when (:compile-toplevel :load-toplevel)
  (defconstant +vec-branch-rate+ 16)
  (defconstant +max-depth+ (1- (floor (log array-dimension-limit +vec-branch-rate+)))))

(deftype depth ()
  `(integer 0 ,+max-depth+))

(deftype chunk ()
  "A contiguous segment of a trie"
  `(simple-vector ,+vec-branch-rate+))

(eval-when (:compile-toplevel :load-toplevel)
  (defstruct (uninit (:predicate uninitp))
    "Sentinel value for uninitialized elements of tries."))

(define-constant +uninit+ (make-uninit)
  :test (lambda (lhs rhs)
          (and (uninitp lhs) (uninitp rhs)))
  :documentation "Sentinel value for uninitialized elements of tries.

Test for this using `uninitp', not `eq' on this constant.")

(defmethod print-object ((obj uninit) stream)
  (write-string "#." stream)
  (write '+uninit+ :stream stream))

(declaim (ftype (function ((g:generator t &optional)) (values chunk &optional))
                alloc-chunk))
(defun alloc-chunk (contents-iterator
                    &aux (contents (g:concatenate contents-iterator (g:always +uninit+))))
  "Construct a `chunk' with elements taken from CONTENTS-ITERATOR, and remaining elements set to `+uninit+'"
  (let* ((arr (make-array +vec-branch-rate+)))
    (iter (declare (declare-variables))
      (for (the fixnum i) below +vec-branch-rate+)
      (setf (svref arr i) (g:next contents)))
    arr))

(deftype chunk-index ()
  "An index into a `chunk'"
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
   :type (or chunk uninit))
  (tail +empty-tail+
   :type tail-buf))

;;; indexing into immutable-vectors

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

(declaim (ftype (function (depth array-index) (values chunk-index array-index &optional))
                index-at-depth)
         (inline index-at-depth))
(defun index-at-depth (depth index)
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
      (multiple-value-bind (curr remaining) (index-at-depth depth idx)
        (trieref (svref body curr) (1- depth) remaining))))

(declaim (ftype (function (t chunk depth array-index) (values t &optional))
                (setf trieref)))
(defun (setf trieref) (new-elt body depth idx)
  (if (zerop depth)
      (setf (svref body idx) new-elt)
      (multiple-value-bind (curr remaining) (index-at-depth depth idx)
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

;;; constructing immutable-vectors

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
                          (values (or chunk uninit) &optional))
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
  (cond ((zerop length) +uninit+)
        ((zerop depth) (alloc-chunk contents))
        (:otherwise (alloc-chunk (chunks-generator (1- depth) length contents)))))

(declaim (ftype (function (array-length) (values array-length &optional))
                length-without-partial-chunks))
(defun length-without-partial-chunks (total-length)
  (* +vec-branch-rate+ (floor total-length +vec-branch-rate+)))

(declaim (ftype (function (chunk-index (g:generator t &rest t))
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

;;; the push-back operator

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

(declaim (ftype (function ((or chunk uninit) chunk depth array-length)
                          (values chunk &optional))
                grow-trie))
(defun grow-trie (trie new-chunk depth new-length)
  "Return a new trie of DEPTH and LENGTH which is like TRIE but with NEW-CHUNK stuck on the end.

TRIE must have DEPTH, must have length of (- NEW-LENGTH (length NEW-CHUNK)), and must have space for at least
one more chunk while staying at DEPTH."
  ;; you'll always have to allocate exactly one new spine node at each depth.
  (cond ((zerop depth) new-chunk)
        ((uninitp trie) (wrap-in-spine depth new-chunk))
        (t
         (let* ((length-before-in-elts (- new-length (length new-chunk)))
                (elts-per-chunk (elts-per-chunk (1- depth)))
                (length-before-in-chunks (floor length-before-in-elts
                                                elts-per-chunk))
                ;; OPTIMIZE: there's potential to do a bit-shift here instead of a multiply, and to convince
                ;; sbcl that the result will fit in a fixnum.
                (length-in-last-chunk (- new-length (* length-before-in-chunks elts-per-chunk))))
           (alloc-chunk (g:concatenate (g:take (g:generate-vector trie) length-before-in-chunks)
                                       (g:generate-these (grow-trie (svref trie length-before-in-chunks)
                                                                    new-chunk
                                                                    (1- depth)
                                                                    ;; FIXME: pass correct size of final chunk when less than ELTS-PER-CHUNK
                                                                    length-in-last-chunk))))))))

(declaim (ftype (function (t immutable-vector) (values immutable-vector &optional))
                push-back))
(defun push-back (new-element vec)
  (with-accessors ((depth %vec-depth)
                   (length %vec-length)
                   (tail %vec-tail)
                   (body %vec-body))
      vec
    (cond ((tail-has-room-p tail)
           ;; fast path when your tail is short: make it longer
           (copy-vec vec
                     :tail (vector-push-back new-element tail)
                     :length (1+ length)))
          ((= (body-length vec) (max-length-at-depth depth))
           ;; fast path when your tail and body are both full: grow an extra layer of depth, put your old tail
           ;; in the newly-expanded body, then grow a new tail
           (copy-vec vec
                     :depth (1+ depth)
                     :length (1+ length)
                     :body (alloc-chunk (g:generate-these body
                                                          (wrap-in-spine depth tail)))
                     :tail (vector new-element)))
          (t
           ;; slow path: move your full tail into your not-full body, trying your best to preserve as much
           ;; structure as possible, then grow a new tail.
           (copy-vec vec
                     :depth depth
                     :length (1+ length)
                     :body (grow-trie body tail depth length)
                     :tail (vector new-element))))))

;;; generators of immutable-vector elements

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

(defmethod g:make-generator ((vec immutable-vector))
  (generate-immutable-vector vec))

;;; reading and printing immutable-vectors

(declaim (ftype (function (stream character (or null fixnum))
                          (values immutable-vector &optional))
                read-vec))
(defun read-vec (stream open infix)
  (declare (ignore infix open))
  (let* ((elts (read-delimited-list #\] stream t))
         (len (length elts)))
    (make-vec len (g:generate-list elts))))

(nr:defreadtable immutable-vector-readtable
  (:merge :standard)
  (:dispatch-macro-char #\# #\[ #'read-vec)
  (:syntax-from :standard #\) #\]))

(defmethod print-object ((vec immutable-vector) stream
                         &aux (gen (generate-immutable-vector vec)))
  (write-string "#[" stream)
  (multiple-value-bind (foundp elt) (g:try-next gen nil)
    (when foundp
      (write elt :stream stream)))
  (g:do-generator (elt gen)
    (write-char #\space stream)
    (write elt :stream stream))
  (write-string "]" stream))

;;; public conversion functions

(declaim (ftype (function (list)
                          (values immutable-vector &optional))
                list-vec))
(defun list-vec (list)
  (make-vec (length list)
            (g:generate-list list)))

(declaim (ftype (function (vector)
                          (values immutable-vector &optional))
                vector-vec))
(defun vector-vec (vector)
  (make-vec (length vector)
            (g:generate-vector vector)))

(declaim (ftype (function (immutable-vector)
                          (values list &optional))
                vec-list))
(defun vec-list (vec)
  (g:collect-to-list (generate-immutable-vector vec)))

(declaim (ftype (function (immutable-vector)
                          (values vector &optional))
                vec-vector))
(defun vec-vector (vec)
  (g:collect-to-vector (generate-immutable-vector vec)))

