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

#|
(definec which-side (lc :count b :side rc :count) :tl
  (declare (ignorable lc rc))
  (if (equal b 'left)
    (alg-left lc b rc)
    (alg-right lc b rc)))
|#

(definec alg-left (lc :count b :side rc :count) :tl
  (declare (ignorable lc b rc))
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           (equal b 'left))
  (move 2 2 'right))
   ;((= (second lc) 4) (move 0 4 'right))
   ;((> (first lc) 4) (move 4 0 'right))
   ;((< (first lc) 4) (move (first lc) 0 'right))))

(definec alg-right (lc :count b :side rc :count) :tl
  (declare (ignorable lc b rc))
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           (equal b 'right))
  (move 1 1 'left))#|ACL2s-ToDo-Line|#

   ;(t (move 1 0 'left))))
#|
(definec alg-final (lc :count b :side rc :count) :tl
  (declare (ignorable lc b rc))
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           (and (= (first lc) (second lc))
                (= (first rc) (second rc))
                (= (first lc) 4)
                (= (second lc) 4))
  (list (move 0 4 'right)
        (
|#

(definec alg-help (lc :count b :side rc :count) :tl
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           (implies (equal b 'left)
                    (>= (first lc) 4))
           (implies (equal b 'right)
                    (and (> (first rc) 0)
                         (>= (first lc) 3)))
           (and (= (first lc) (second lc))
                (= (first rc) (second rc))))
           #|
           (implies (= (second rc) 0)
                    (equal b 'left))
           (implies (>= (second lc) 4)
                    (and (= (first lc) (second lc))
                         (= (first rc) (second rc))))
           (implies (and (< (second lc) 4)
                         (equal b 'left))
                    (= (second lc) 0))
           (implies (= (second rc) 0)
                    (= (first rc) 0))
           (implies (> (second rc) 0)
                    (> (first rc) 0)))|#
                    
  (cond
   ((and (= (first lc) 4)
         (= (second lc) 4)
         (equal b 'left)) (list (move 0 4 'right)
                                (move 1 0 'left)
                                (move 4 0 'right)
                                (move 1 0 'left)
                                (move 2 0 'right)))
   ((equal b 'left) (cons (move 2 2 'right)
                          (alg-help (list (- (first lc) 2)
                                          (- (second lc) 2))
                                    'right
                                    (list (+ (first rc) 2)
                                          (+ (second rc) 2)))))
                                          
   ((equal b 'right) (cons (move 1 1 'left)
                          (alg-help (list (+ (first lc) 1)
                                          (+ (second lc) 1))
                                    'left
                                    (list (- (first rc) 1)
                                          (- (second rc) 1)))))))

;
(definec simplealg (lc :count b :side rc :count) :tl
  (declare (ignorable b rc))
  :ic (and (and (= (first rc) 0)
                (= (second rc) 0))
           (= (first lc) (second lc))
           (equal b 'left))
  (cond 
   ((= (first lc) 0) '())
   ((<= (+ (first lc) (second lc)) 4) (move (first lc) (second lc) 'right))
   ((= (first lc) 3) (list (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)))
   ((= (first lc) 4) (list (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)
                           (move 1 1 'left)
                           (move 2 2 'right)))
   (t (alg-left lc b rc))))


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



