(include-book "arithmetic-5/top" :dir :system)

(defun toy-enc-step (x)
  (declare (xargs :guard (and (natp x)   (< x #x100000000))))
  (mod (+ x 1) #x100000000))

(defun toy-dec-step (x)
  (declare (xargs :guard (and (natp x)   (< x #x100000000))))
  (mod (- x 1) #x100000000))

(defthm toy-enc-step-natp
  (implies (and (natp x) (< x #x100000000))
           (and (natp (toy-enc-step x))
                (< (toy-enc-step x) #x100000000))))


(defthm toy-dec-step-natp
  (implies (and (natp x) (< x #x100000000))
           (and (natp (toy-dec-step x))
                (< (toy-dec-step x) #x100000000))))

(defthm toy-enc-dec-step-invertible
  (implies (and (natp x) (< x #x100000000))
           (equal (toy-dec-step (toy-enc-step x)) x)))


(defun toy-enc (x rounds)
  (declare (xargs :guard (and (natp x) (< x #x100000000) 
                              (natp rounds))
                  :verify-guards nil))
  (if (zp rounds)
      x
    (toy-enc-step (toy-enc x (- rounds 1)))))

(defthm toy-enc-natp
  (implies (and (natp x) (< x #x100000000) (natp rounds))
           (and (natp (toy-enc x rounds))
                (< (toy-enc x rounds) #x100000000))))

(verify-guards toy-enc)

(defun toy-dec-alt (x rounds)
  (declare (xargs :guard (and (natp x) (< x #x100000000) 
                              (natp rounds))
                  :verify-guards nil))
  (if (zp rounds)
      x
    (toy-dec-step (toy-dec x (- rounds 1)))))


(defun toy-dec (x rounds)
  (declare (xargs :guard (and (natp x) (< x #x100000000) 
                              (natp rounds))
                  :verify-guards nil))
  (if (zp rounds)
      x
    (toy-dec (toy-dec-step x) (- rounds 1))))  ;; Recursively call toy-dec with toy-dec-step inside


(defthm toy-dec-natp
  (implies (and (natp x) (< x #x100000000) (natp rounds))
           (and (natp (toy-dec x rounds))
                (< (toy-dec x rounds) #x100000000))))

(verify-guards toy-dec-alt)
(verify-guards toy-dec)

(defthm toy-dec-alt-equal-to-toy-dec
  (implies (and (natp x) (natp rounds) (< x #x100000000))
           (equal (toy-dec-alt x rounds)
                  (toy-dec x rounds))))


(in-theory (disable toy-enc-step))
(in-theory (disable toy-dec-step))

(defthm toy-enc-dec-invertible
  (implies (and (natp x) (< x #x100000000)
                (natp rounds))
            (equal (toy-dec (toy-enc x rounds) rounds)
                    x)))

(equal 2 (toy-dec (toy-enc 2 3) 3))
(equal 100 (toy-dec (toy-enc 100 234) 234))
(equal 100000 (toy-dec (toy-enc 100000 567) 567))


