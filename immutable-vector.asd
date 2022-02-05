(defsystem "immutable-vector"
  :class :package-inferred-system
  :author "Phoebe Goldman"
  :version "0.0.1"
  :depends-on ("immutable-vector/immutable-vector")
  :in-order-to ((test-op (test-op "immutable-vector/test"))))

(defsystem "immutable-vector/test"
  :defsystem-depends-on ((:version "fiveam-asdf" "3.0.1"))
  :class :package-inferred-fiveam-tester-system
  :depends-on ("immutable-vector/test/package")
  :test-names ((#:immutable-vector-suite . :immutable-vector/test/package)))
