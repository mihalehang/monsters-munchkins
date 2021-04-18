; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(set-ccg-time-limit nil)
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

;; data definitions for types of moves
(defdata move-left (list 'move nat 'monsters 'and nat 'munchkins 'to 'the 'left))
(defdata move-right (list 'move nat 'monsters 'and nat 'munchkins 'to 'the 'right))
(defdata move (oneof move-left move-right))

; data definitions for types of list of moves
(defdata lom-start-left (oneof '()
                               (cons move-right '())
                               (cons move-right (cons move-left lom-start-left))))
(defdata lom-start-right (oneof '()
                                (cons move-left '())
                               (cons move-left (cons move-right lom-start-right))))
(defdata lom (oneof lom-start-left lom-start-right))

; helper function for the algorithm, recursively deals with cases
; where there are more than 4 starting monsters and munchkins
(definec alg-help (lc :count b :side rc :count) :tl
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

; algorithm for solving a game of monsters and munchkins
(definec alg (lc :count b :side rc :count) :tl
  (declare (ignorable b rc))
           ;; both sides must have an equal amount of monsters and
           ;; munchkins
  :ic (and (= (first rc) (second rc))
           (= (first lc) (second lc))
           ;; boat starts on left when game begins
           (equal b 'left))
  (cond 
   ;; if no monsters or munchkins, no moves
   ((= (first lc) 0) '())
   ;; if total monsters and munchkins are less than boat capacity,
   ;; move them all over
   ((<= (+ (first lc) (second lc)) 4) (move (first lc) (second lc) 'right))
   ;; hardcoded case with 3 monsters and 3 munchkins
   ((= (first lc) 3) (list (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)))
   ;; hardcoded case with 4 monsters and 4 munchkins
   ((= (first lc) 4) (list (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)))
   ;; if more complicated case, call helper
   (t (alg-help lc b rc))))

; simulate a single move in the game
(definec simulate-move (m :move lc :count b :side rc :count) :tl
  (declare (ignorable b))
      ; if the boat is on the left side, move should be towards right
      ; (and vice versa)
  :ic (if (equal b 'left)
        (move-rightp m)
        (move-leftp m))
  ;; update lc, b, and rc depending on move
  (if (move-rightp m)
    (list 
     (list (- (first lc) (second m))
           (- (second lc) (fifth m)))
     'right
     (list (+ (first rc) (second m))
           (+ (second rc) (fifth m))))
    (list
     (list (+ (first lc) (second m))
           (+ (second lc) (fifth m)))
     'left
     (list (- (first rc) (second m))
           (- (second rc) (fifth m))))))#|ACL2s-ToDo-Line|#

#|
(definec check-move (m :move lc :count b :side rc :count) :boolean
  :ic (if (equal b 'left)
        (move-rightp m)
        (move-leftp m))
  (if (equal b 'left)
    (and (<= (second m) (first lc))
         (<= (fifth m) (second lc)))
    (and (<= (second m) (first rc))
         (<= (fifth m) (second rc)))))
|#
    
; simulate the execution of a list of moves in a game
(definec simulate (lom :lom lc :count b :side rc :count) :tl
  :ic (if (equal b 'left)
        (lom-start-leftp lom)
        (lom-start-rightp lom))
  (cond
   ((endp lom) (list lc b rc))
   ((consp lom) (simulate (rest lom)
                          (first (simulate-move (first lom) lc b rc))
                          (second (simulate-move (first lom) lc b rc))
                          (third (simulate-move (first lom) lc b rc))))))
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



