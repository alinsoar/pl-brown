((lambda (self n)
   (self self n))
 (lambda (self n)
   (if (= n 0)
       0
       (+ n (self self (- n 1)))))
 10)

