
;; Termination proof of Traditional Algorithm

;(set-termination-method :measure)
;(set-well-founded-relation n<)
;(set-defunc-typed-undef nil)
;(set-defunc-generalize-contract-thm nil)
;(set-gag-mode nil)

;; Represents the number of Monsters
;(defdata monsters nat)
;; Represents the number of Munchkins
;(defdata munchkins nat)
;; Represents the capacity of the boat
;(defdata capacity nat)
;; Represents which side the boat is on
(defdata side (oneof 'left 'right))

;; Direction statement
(definec move (mon :nat mun :nat side :side) :tl
  (list 'move mon 'monsters 'and mun 'munchkins 'to 'the side))

;; Number of Monsters and Munchkins respectively on a river bank
(defdata count (list nat nat))

;(set-ignore-ok t)

;; Measure function

(definec alg-help-measure (lc :count b :side) :nat 
  (if (and (equal b 'left) (! (and (= (first lc) 4)
         (= (second lc) 4))))
    (1+ (first lc)) 0))

; helper function for the algorithm, recursively deals with cases
; where there are more than 4 starting monsters and munchkins
(definec alg-help (lc :count b :side rc :count) :tl
  ;(declare (xargs :measure (if (and (countp lc) (sidep b) (countp rc)) (alg-measure lc b rc) 0)))
           ;; must have equal monsters and munchkins
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           ;; must have more than 4 monsters and 4 munchkins
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           ;; left side must have 4 or more munchkins
           (implies (equal b 'left)
                    (>= (second lc) 4))
           ;; both sides must have an equal amount of monsters and munchkins
           ;; (case where you move all munchkins over is hardcoded in first
           ;; branch, so you don't need to account for this in contracts)
           (and (= (first lc) (second lc))
                (= (first rc) (second rc))))
                    
  (cond
   ;; hard code last steps, once there are 4 munchkins on left side
   ((and (= (first lc) 4)
         (= (second lc) 4)
         (equal b 'left)) (list (move 0 4 'right)
                                (move 1 0 'left)
                                (move 4 0 'right)
                                (move 1 0 'left)
                                (move 2 0 'right)))
   ;; recursively bring 2 pairs over, 1 pair back
   ((equal b 'left) (cons (move 2 2 'right)
                          (cons (move 1 1 'left)
                          (alg-help (list (- (first lc) 1)
                                          (- (second lc) 1))
                                    'left
                                    (list (+ (first rc) 1)
                                          (+ (second rc) 1))))))))

;; Termination Proof
Conjecture alg-help-terminates:
(implies (and (countp lc)
              (= (first lc) (second lc))
              (> (second lc) 4)
              (sidep b)
              (equal b 'left))
         (< (alg-help-measure (list (- (first lc) 1) (second lc)) b)
            (alg-help-measure lc b)))

Context:
C1. (countp lc)
C2. (= (first lc) (second lc))
C3. (> (second lc) 4)
C4. (sidep b)
C5. (equal b 'left)

Derived Context:
D1. (countp (list (1- (first lc)) (second lc))) {Def countp, car-cdr axioms, C1, C2, C3}

Goal:
(< (alg-help-measure (list (1- (first lc)) (second lc)) b)
            (alg-help-measure lc b))

Proof:
(alg-help-measure lc b)
= {Def alg-help-measure, C1, C2, C3, C4, C5}
(+ (first lc) 1)
> {Arith}
(first lc)
= {Def alg-help-measure, car-cdr axioms, C1, C2, C3, C4, C5, D1}
(alg-help-measure (list (1- (first lc)) (second lc)) b)

QED

;; have a fxn thats not recursive, no need to do a termination argument
;; all it does is expand to other function calls that terminates.
;; assume everything terminates already (this is referring to alg)
;; so, shown alg-help-terminates, got rid of hypo that doesn't terminates
;; shows it's true, it's always decreasing, 
;; know that alg terminates because it only calls terminate or other things terminate
;; ^^ argument for termination of alg in addition to ACL2s also terminating
;; bewteen boat on left and right and left, number of monsters on left
;; always decreasing the number of monsters, add back more monsters