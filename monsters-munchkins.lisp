;; Represents the number of Monsters
(defdata monsters nat)
;; Represents the number of Munchkins
(defdata munchkins nat)
;; Represents the capacity of the boat
(defdata capacity nat)
;; Represents which side the boat is on
(defdata side (oneof 'left 'right))

;; Direction statement
(defun move (mon mun side)
  (list 'move mon 'monsters 'and mun 'munchkins 'to 'the side))

;; Number of Monsters and Munchkins respectively on left bank
(defdata left-count (list monsters munchkins))

;; Number of Monsters and Munchkins respectively on left bank
(defdata right-count (list monsters munchkins))

;; Capacity and the side the boat is on
(defdata boat (list capacity side))

;; DONT FORGET TO WRITE CONTRACTS YALL ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Traditional Algorithm

;; Prints the directions in case that the 
;; Monsters and Munchkins counts are greater than 4
(defun helper (lc b rc)
  (cond 
   ((and (> (second lc) 4)
         (equal (second b) 'left)) (cons (move 2 2 'right)
                                         (helper (list (- (first lc) 2) 
                                                       (- (second lc) 2))
                                                 (list 4 'right)
                                                 (list (+ (first rc) 2)
                                                       (+ (second rc) 2)))))
   ((and (>= (second lc) 4)
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
                                                 (list (+ (second rc) 4)
                                                       (second lc)))))
   ((and (<= (first lc) 4)
         (equal (second b) 'left)) (move (first lc) 0 'right))
   (t (cons (move 1 0 'left)
            (helper (list (+ (first lc) 1)
                          (second lc))
                    (list 4 'left)
                    (list (- (first rc) 1)
                          (second rc)))))))
            

;; Prints the rest of the moves
(defun tradalg (lc b rc)
  (cond 
   ((and (= (first lc) 0) (= (second lc) 0)) '())
   ((<= (+ (first lc) (second lc)) 4) (move (first lc) (second lc) 'right))
   ((= (second lc) 3) (list (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)))
   ((= (second lc) 4) (list (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)
                            (move 1 1 'left)
                            (move 2 2 'right)))
   ((> (second lc) 4) (helper lc b rc))))



