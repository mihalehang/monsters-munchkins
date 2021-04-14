

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

;; Capacity and the side the boat is on
(defdata boat (list nat side))

;; Traditional Algorithm

;; Shouldn't have a function this long, running out of time to prove all of them
;; Solution: simplify it into even more helper functions
;; Move left and move right function... try to split off changes into other functions

;; Prints the directions in case that the 
;; Monsters and Munchkins counts are greater than 4
(definec helper (lc :count b :boat rc :count) :tl
           ;; number of munchkins = number of monsters
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           ;; ignore hardcoded cases from main function
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           ;; if more than 0 munchkins on left side, 
           ;; there should be more munchkins than monsters on left
           (implies (not (zp (second lc)))
             (>= (second lc) (first lc)))
           ;; if more than 0 munchkins on right side, 
           ;; there should be more munchkins than monsters on right
           (implies (not (zp (second rc)))
             (>= (second rc) (first rc)))
           ;; if more than 0 munchkins on right side and
           ;; boat is on the right side, there should be 
           ;; more munchkins than monsters on right and there
           ;; should be more than 0 monsters
           (implies (and (not (zp (second rc)))
                         (equal (second b) 'right))
             (and (>= (second rc) (first rc))
                  (> (first rc) 0)))
           ;; if 0 munchkins on right side there should 
           ;; also be 0 monsters on right side
           (implies (zp (second rc))
                    (zp (first rc))))
  (cond 
   ((and (> (second lc) 4)
         (equal (second b) 'left)) (cons (move 2 2 'right)
                                         (helper (list (- (first lc) 2) 
                                                       (- (second lc) 2))
                                                 (list 4 'right)
                                                 (list (+ (first rc) 2)
                                                       (+ (second rc) 2)))))
   ((and (> (second lc) 0)
         (equal (second b) 'right)) (cons (move 1 1 'left)
                                         (helper (list (+ (first lc) 1) 
                                                       (+ (second lc) 1))
                                                 (list 4 'left)
                                                 (list (- (first rc) 1)
                                                       (- (second rc) 1)))))
   ((and (= (second lc) 4)
         (equal (second b) 'left)) (cons (move 0 4 'right)
                                         (helper (list (first lc)
                                                       (- (second lc) 4))
                                                 (list 4 'right)
                                                 (list (first rc)
                                                       (+ (second rc) 4)))))
   ((and (> (first lc) 4)
         (equal (second b) 'left)) (cons (move 4 0 'right)
                                         (helper (list (- (first lc) 4)
                                                       (second lc))
                                                 (list 4 'right)
                                                 (list (+ (first rc) 4)
                                                       (second rc)))))
   ((and (<= (first lc) 4)
         (equal (second b) 'left)) (list (move (first lc) 0 'right)))
   (t (cons (move 1 0 'left)
            (helper (list (+ (first lc) 1)
                          (second lc))
                    (list 4 'left)
                    (list (- (first rc) 1)
                          (second rc)))))))

;; find case that is terminating over time
;; running out of time to terminate
;; look for thing that is changing over time
;; measure function, decreasing in every time step
;; measure function has to decrease every time on the recursive calls
;; figure out the measure function, closer to base case, base case will run
;; proof will be a termination proof about helper
;; termination proof is not enough to prove validity


;; correctness proof => if (valid initial state), returns a valid final state
;; if execute moves, all on the right side
;; need a way to show that the steps get to the right state

;; 1) function that takes in a list of moves and initial state => final state
;; 2) (test? '(implies ...)) focus on this part FIRST
;; 3) then think about prove algo is correct, part of that is defthm
;; (if (and (s is a valid state) (l is a list of moves from running (helper s))) 
;;  then the result of simulating l from state s is a valid final state)
;; (test? '(implies ...))

;; function that simulates moves (way easier)
;; takes in list of moves and initial state => gives back final state
;; move blank to blank and then does it, gives final state

#|
To-Do
- write a measure function (termination proof is the meat)
- write a simulator, (initial state and list of moves => execute them properly)
- (test? '(implies ...))
- after completion of (test? ...) then reach out to Josh :)
- no need to broaden the invariants
|#

;
;(definec (lc :count b :boat rc :count) :tl
  ;(

;; Prints the rest of the moves
(defun tradalg (lc b rc)
  (cond 
   ((and (= (first lc) 0) (= (second lc) 0)) '())
   ((and (<= (+ (first lc) (second lc)) 4)
         (equal (second b) 'left)) (move (first lc) (second lc) 'right))
   ((and (= (second lc) 3) (list (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)))
   ((= (second lc) 4) (list (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)))
   (t (helper lc b rc))))



