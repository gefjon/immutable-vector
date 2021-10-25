(uiop:define-package :immutable-vector/immutable-vector
  (:nicknames :immutable-vector)
  (:import-from :alexandria
                #:array-index #:array-length)
  (:use :cl :iterate))
(in-package :immutable-vector/immutable-vector)

(eval-when (:compile-toplevel :load-toplevel)
  (defconstant +vec-branch-rate+ 16)
  (defconstant +max-depth+ (1- (floor (log array-dimension-limit +vec-branch-rate+)))))

(deftype depth ()
  `(integer 0 ,+max-depth+))

(deftype vec-backing-array ()
  `(simple-vector ,+vec-branch-rate+))

(declaim (ftype (function () (values vec-backing-array &optional))
                alloc-backing-array))
(defun alloc-backing-array ()
  (make-array +vec-branch-rate+ :initial-element '#:uninit))

(deftype one-index ()
  `(integer 0 (,+vec-branch-rate+)))

(defstruct (immutable-vector
            (:constructor %make-vec)
            (:copier nil)
            (:conc-name %vec-))
  (depth (error "supply :depth to %make-vec")
   :type depth)
  (length (error "supply :length to %make-vec")
   :type array-length)
  (body (error "supply :body to %make-vec")
   :type vec-backing-array)
  (head nil
   :type (or null simple-vector))
  (tail nil
   :type (or null simple-vector)))

(deftype iterator (&optional (element-type t))
  `(function () (values (or null ,element-type) (or null array-index))))

(declaim (ftype (function (immutable-vector) (values array-index &optional))
                head-length tail-length length-before-tail length-after-head body-length))
(defun head-length (vec &aux (head (%vec-head vec)))
  (if head (length head) 0))
(defun tail-length (vec &aux (tail (%vec-tail vec)))
  (if tail (length tail) 0))
(defun length-after-head (vec)
  (- (%vec-length vec) (head-length vec)))
(defun length-before-tail (vec)
  (- (%vec-length vec) (tail-length vec)))
(defun body-length (vec)
  (- (%vec-length vec)
     (head-length vec)
     (tail-length vec)))

(declaim (ftype (function (immutable-vector array-index) (values boolean &optional))
                index-in-head-p index-in-tail-p))
(defun index-in-head-p (vec idx &aux (head (%vec-head vec)))
  "True if IDX is within the head part of VEC, nil otherwise.

Does not necessarily imply that IDX is in-bounds for VEC."
  (and head
       (< idx (length head))))
(defun index-in-tail-p (vec idx &aux (tail (%vec-tail vec)))
  "True if IDX is within the tail part of VEC, nil otherwise.

Does not necessarily imply that IDX is in-bounds for VEC."
  (and tail
       (> idx (length-before-tail vec))))

(declaim (ftype (function (immutable-vector array-index) (values t &optional))
                headref tailref))
(defun headref (vec idx)
  "aref into the tail of VEC. IDX must be in-bounds for VEC, and must be `index-in-head-p'"
  (svref (%vec-head vec) idx))
(defun tailref (vec idx)
  "aref into the tail of VEC. IDX must be in-bounds for VEC, and must be `index-in-tail-p'"
  (svref (%vec-tail vec) (- idx (length-before-tail vec))))

(declaim (ftype (function (depth array-index) (values one-index array-index &optional))
                depth-index)
         (inline depth-index))
(defun depth-index (depth index)
  (let ((depth-low-bit (* depth 4)))
    (values (ldb (byte 4 depth-low-bit)
                 index)
            (ldb (byte depth-low-bit 0)
                 index))))

(declaim (ftype (function (immutable-vector array-index) (values array-index &optional))
                body-index))
(defun body-index (vec idx)
  (- idx (head-length vec)))

(declaim (ftype (function (vec-backing-array depth array-index) (values t &optional))
                trieref))
(defun trieref (body depth idx)
  (if (zerop depth)
      (svref body idx)
      (multiple-value-bind (curr remaining) (depth-index depth idx)
        (trieref (svref body curr) (1- depth) remaining))))

(declaim (ftype (function (t vec-backing-array depth array-index) (values t &optional))
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
  "aref into the body part of VEC. IDX must be in-bounds for vec, and must be neither `index-in-head-p' nor `index-in-tail-p'."
  (trieref (%vec-body vec) (%vec-depth vec) (body-index vec idx)))

(declaim (ftype (function (array-index) (values depth &optional))
                length-required-depth))
(defun length-required-depth (length)
  (case length
    ((0 1) 0)
    (t (values (floor (log (1- length) 16))))))

(declaim (ftype (function (depth array-index)
                          (values vec-backing-array &optional))
                alloc-trie))
(defun alloc-trie (depth length)
  ;;; FIXME: we over-allocate (by a lot), e.g. in (alloc-tree 2 257)
  (assert (<= 0 length (expt +vec-branch-rate+ (1+ depth))))
  (if (zerop depth)
      (alloc-backing-array)
      (iter (declare (declare-variables))
        (with trie = (alloc-backing-array))
        (with per-chunk-length = (expt +vec-branch-rate+ depth))
        (with n-chunks = (ceiling (/ length per-chunk-length)))
        (for i below n-chunks)
        (for length-so-far = (* i per-chunk-length))
        (setf (svref trie i) (alloc-trie (1- depth)
                                         (min per-chunk-length
                                              (- length length-so-far))))
        (finally (return trie)))))

(declaim (ftype (function ((and array-index (integer (0)))
                           iterator)
                          (values vec-backing-array &optional))
                make-trie))
(defun make-trie (length contents)
  (let* ((depth (length-required-depth length))
         (trie (alloc-trie depth length)))
    (iter (declare (declare-variables))
      (for (the fixnum i) below length)
      (for (values elt eltp) = (funcall contents))
      (assert (and eltp (= eltp i)))
      (setf (trieref trie depth i) elt))
    trie))

(declaim (ftype (function (immutable-vector) (values iterator &optional))
                immutable-vector-iterator))
(defun immutable-vector-iterator (vec)
  "Return a closure of no arguments which, on successive calls, returns successsive elements of VEC and their indices, or (values nil nil) once all elements are exhausted."
  (let* ((current-index -1))
    (declare (type (or array-index (eql -1)) current-index))
    (labels ((inbounds-advance ()
               (incf current-index)
               (cond ((index-in-head-p vec current-index)
                      (values (headref vec current-index) t))
                     ((index-in-tail-p vec current-index)
                      (values (tailref vec current-index) t))
                     ;; FIXME: optimize to not walk the table on each step by keeping a handle on the current
                     ;; chunk, or a stack of chunks?
                     (t (values (bodyref vec current-index) t))))
             (vec-iter ()
               (if (>= current-index (1- (%vec-length vec)))
                   (values nil nil)
                   (inbounds-advance))))
      #'vec-iter)))

(declaim (ftype (function (list) (values iterator &optional))
                list-iterator))
(defun list-iterator (list &aux (remaining list) (current-index -1))
  (declare (fixnum current-index)
           (list remaining))
  (flet ((iter-list ()
           (if (null remaining) (values nil nil)
               (values (pop remaining) (incf current-index)))))
    #'iter-list))

(declaim (ftype (function (array-index) (values iterator &optional))
                upto-iterator))
(defun upto-iterator (limit &aux (next -1))
  (lambda ()
    (if (= next limit) (values nil nil)
        (let* ((n (incf next))) (values n n)))))

(declaim (ftype (function (immutable-vector &key (:depth depth)
                                            (:length array-length)
                                            (:body vec-backing-array)
                                            (:head (or null simple-vector))
                                            (:tail (or null simple-vector)))
                          (values immutable-vector &optional))
                copy-vec))
(defun copy-vec (vec &key (depth (%vec-depth vec))
                       (length (%vec-length vec))
                       (body (%vec-body vec))
                       (head (%vec-head vec))
                       (tail (%vec-tail vec)))
  (%make-vec :depth depth
             :length length
             :body body
             :head head
             :tail tail))

(declaim (ftype (function (simple-vector) (values boolean &optional))
                head-or-tail-has-room-p))
(defun head-or-tail-has-room-p (head-or-tail)
  (< (length head-or-tail)
     +vec-branch-rate+))

(declaim (ftype (function (t simple-vector) (values simple-vector &optional))
                vector-push-front vector-push-back))
(defun vector-push-front (new-element vec
                          &aux (new (make-array (1+ (length vec)))))
  (setf (svref new 0) new-element)
  (iter (declare (declare-variables))
    (for elt in-vector vec with-index i)
    (setf (svref new (1+ i)) elt))
  new)
(defun vector-push-back (new-element vec
                         &aux (new (make-array (1+ (length vec)))))
  (iter (declare (declare-variables))
    (for elt in-vector vec with-index i)
    (setf (svref new i) elt))
  (setf (svref new (length vec)) new-element)
  new)

(declaim (ftype (function (t immutable-vector) (values immutable-vector &optional))
                push-front push-back))
(defun push-front (new-element vec)
  (cond ((null (%vec-head vec))
         (copy-vec vec :head (vector new-element)))
        ((head-or-tail-has-room-p (%vec-head vec))
         (copy-vec vec :head (vector-push-front new-element (%vec-head vec))))
        ((error "unimplemented"))))
(defun push-back (new-element vec)
  (cond ((null (%vec-tail vec))
         (copy-vec vec :tail (vector new-element)))
        ((head-or-tail-has-room-p (%vec-tail vec))
         (copy-vec vec :tail (vector-push-back new-element (%vec-tail vec))))
        ((error "unimplemented"))))

;; (declaim (ftype (function (immutable-vector immutable-vector)
;;                           (values immutable-vector &optional))
;;                 vec-conc-2))
;; (defun vec-conc-2 (left right)
;;   (let* ((new-len (+ (%vec-length left) (%vec-length right))))
;;     ))
