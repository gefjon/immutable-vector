(uiop:define-package :immutable-vector/test/package
  (:use :cl :fiveam :iterate :immutable-vector/immutable-vector)
  (:local-nicknames (:g :generator)))
(in-package :immutable-vector/test/package)

(def-suite immutable-vector-suite)

(defun call-quietly (thunk)
  (let* ((*test-dribble* (make-broadcast-stream)))
    (funcall thunk)))

(defmacro quietly (&body body)
  `(call-quietly (lambda () ,@body)))

(def-test from-list (:suite immutable-vector-suite)
  (for-all ((list (gen-list :length (gen-integer :min 0 :max 4096))))
    (let* ((vec (list-vec list)))
      (quietly ;; avoid printing thousands of dots
        (iter (for i upfrom 0)
          (for elt in list)
          (is (equal elt (vecref vec i)))))
      (is (equal list (vec-list vec))))))

(def-test from-vector (:suite immutable-vector-suite)
  (for-all ((list (gen-list :length (gen-integer :min 0 :max 4096))))
    (let* ((vector (coerce list 'vector))
           (vec (vector-vec vector)))
      (quietly 
        (iter (for elt in-vector vector with-index i)
          (is (equal elt (vecref vec i)))))
      (is (equalp vector (vec-vector vec))))))
