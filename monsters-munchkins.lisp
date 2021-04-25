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

;;;;;;;;;;;;;; Data definitions ;;;;;;;;;;;;;;;

; This section of the code is dedicated to defining
; data types that we use to represent the Monsters
; and Munchkins game.

; represents a side that the boat can be on
(defdata side (oneof 'left 'right))

; represents a side of a river, where the first element
; is the number of monsters and the second is the number
; of munchkins
(defdata count (list nat nat))

;; data definitions for types of moves
(defdata move-left (list 'move nat 'monsters 'and nat 'munchkins 'to 'the 'left))
(defdata move-right (list 'move nat 'monsters 'and nat 'munchkins 'to 'the 'right))
(defdata move (oneof move-left move-right))

; data definitions for types of list of moves

; starting on the left side of the river
(defdata lom-start-left (oneof '()
                               (cons move-right '())
                               (cons move-right (cons move-left lom-start-left))))
; starting on the right side of the river
(defdata lom-start-right (oneof '()
                                (cons move-left '())
                               (cons move-left (cons move-right lom-start-right))))
(defdata lom (oneof lom-start-left lom-start-right))

; represents a game state
; the boolean field represents an error flag, that is
; set to true when an invalid move is made (used for
; simulate function)
(defdata state (list count side count boolean))

;;;;;;;;;;;;;; Algorithm functions ;;;;;;;;;;;;

; This section of the code is dedicated to functions
; made for the game algorithm. This includes a single
; move function, the main algorithm (alg), and its
; helper (alg-help)

;; returns a list that represents a move in the game
(definec move (mon :nat mun :nat side :side) :move
  (list 'move mon 'monsters 'and mun 'munchkins 'to 'the side))
;; move checks
(check= (move 1 3 'left) '(move 1 monsters and 3 munchkins to the left))
(check= (move 0 4 'right) '(move 0 monsters and 4 munchkins to the right))

; helper function for the algorithm, recursively deals with cases
; where there are more than 4 starting monsters and munchkins
(definec alg-help (lc :count b :side rc :count) :lom-start-left
  (declare (ignorable b))
           ;; must have equal monsters and munchkins
  :ic (and (= (+ (first lc) (first rc)) (+ (second lc) (second rc)))
           ;; must have more than 4 monsters and 4 munchkins
           (> (+ (first lc) (first rc) (second lc) (second rc)) 8)
           ;; left side must have 4 or more munchkins
           (>= (second lc) 4)
           ;; boat must be on the left side
           (equal b 'left)
           ;; both sides must have an equal amount of monsters and munchkins
           ;; (case where you move all munchkins over is hardcoded in first
           ;; branch, so you don't need to account for this in contracts)
           (and (= (first lc) (second lc))
                (= (first rc) (second rc))))
                    
  (cond
   ;; hard code last steps, once there are 4 munchkins on left side
   ((and (= (first lc) 4)
         (= (second lc) 4)) (list (move 0 4 'right)
                                  (move 1 0 'left)
                                  (move 4 0 'right)
                                  (move 1 0 'left)
                                  (move 2 0 'right)))
   ;; recursively bring 2 pairs over, 1 pair back
   (t (cons (move 2 2 'right)
            (cons (move 1 1 'left)
                  (alg-help (list (- (first lc) 1)
                                  (- (second lc) 1))
                            'left
                            (list (+ (first rc) 1)
                                  (+ (second rc) 1))))))))
; alg-help checks
(check= (alg-help '(5 5) 'left '(0 0)) '((MOVE 2 MONSTERS AND 2 MUNCHKINS TO THE RIGHT)
 (MOVE 1 MONSTERS AND 1 MUNCHKINS TO THE LEFT)
 (MOVE 0 MONSTERS AND 4 MUNCHKINS TO THE RIGHT)
 (MOVE 1 MONSTERS AND 0 MUNCHKINS TO THE LEFT)
 (MOVE 4 MONSTERS AND 0 MUNCHKINS TO THE RIGHT)
 (MOVE 1 MONSTERS AND 0 MUNCHKINS TO THE LEFT)
 (MOVE 2 MONSTERS AND 0 MUNCHKINS TO THE RIGHT)))
(check= (alg-help '(27 27) 'left '(1 1)) 
        (cons (move 2 2 'right) 
              (cons (move 1 1 'left) 
                    (alg-help '(26 26) 'left '(0 0)))))
(check= (alg-help '(5 5) 'left '(999 999)) 
        (alg-help '(5 5) 'left '(0 0)))

; algorithm for solving a game of monsters and munchkins
(definec alg (lc :count b :side rc :count) :lom-start-left
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
   ((<= (+ (first lc) (second lc)) 4) (list (move (first lc) (second lc) 'right)))
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
; alg checks
(check= (alg '(0 0) 'left '(0 0)) '())
(check= (alg '(1 1) 'left '(0 0)) (list (move 1 1 'right)))
(check= (alg '(2 2) 'left '(0 0)) (list (move 2 2 'right)))
(check= (alg '(3 3) 'left '(0 0)) (list (move 2 2 'right)
                                        (move 1 1 'left)
                                        (move 2 2 'right)))
(check= (alg '(4 4) 'left '(0 0)) (list (move 2 2 'right)
                                        (move 1 1 'left)
                                        (move 2 2 'right)
                                        (move 1 1 'left)
                                        (move 2 2 'right)))
(check= (alg '(5 5) 'left '(0 0)) (alg-help '(5 5) 'left '(0 0)))

;;;;;;;;;;;;;;; Valid-lom functions ;;;;;;;;;;;;

#|
This section is dedicated to testing the correctness
of our algorithm by checking if the outputted list
of moves is what we expect, based on our initial research
and tinkering with the game. According to our algorithm,
correct solutions should alternate between (move 2 2 'right)
and (move 1 1 'left), until there are 4 munchkins remaining
on the left, whereafter the last moves should be

(list (move 0 4 'right)
      (move 1 0 'left)
      (move 4 0 'right)
      (move 1 0 'left)
      (move 2 0 'right))

With this, we have found that a correct solution should
have a list length of 5 + (2 * (m - 4)), where m is
the initial amount of munchkins on the left side. This
is because the last moves have a length of 5, and before
them the algorithm recursively adds the aforementioned
right and left moves (hence the 2 in the above formula).
It does this until there are 4 munchkins remaining on
the left side, thus the formula has the (m - 4).

Essentially, we'd like to see if, given a valid start
state (defined below), will the solution list satisfy
the above properties.
|#


; check if given state is a valid start
(definec is-valid-start (s :state) :boolean
       ;; boat starts on left side
  (and (equal (second s) 'left)
       ;; equal amount of mons and munches on right side
       (= (first (third s)) (second (third s)))
       ;; equal amount of mons and munches on left side
       (= (first (first s)) (second (first s)))
       ;; monsters and munchkins on left side are both
       ;; greater than 4. This is because the cases
       ;; less than 4 are hardcoded in the alg; we are
       ;; really checking the functionality of alg-help
       (> (first (first s)) 4)
       (> (second (first s)) 4)
       ;; error flag is not activated
       (not (fourth s))))
; is-valid-start checks
(check= (is-valid-start (list '(5 5) 'left '(0 0) nil)) t)
(check= (is-valid-start (list '(5 5) 'right '(0 0) nil)) nil)
(check= (is-valid-start (list '(5 5) 'left '(0 0) t)) nil)
(check= (is-valid-start (list '(6 5) 'left '(0 0) nil)) nil)
(check= (is-valid-start (list '(5 5) 'left '(1 0) nil)) nil)

; checks if a list of moves is equal to the expected
; last moves of a game
(definec last-moves (lom :lom) :boolean
  (equal (list (move 0 4 'right)
               (move 1 0 'left)
               (move 4 0 'right)
               (move 1 0 'left)
               (move 2 0 'right)) lom))
; last-moves checks
(check= (last-moves '()) nil)
(check= (last-moves (list (move 0 4 'right))) nil)
(check= (last-moves (list (move 0 4 'right)
                          (move 1 0 'left)
                          (move 4 0 'right)
                          (move 1 0 'left)
                          (move 2 0 'right))) t)

; given a start state, returns the expected number 
; of moves needed for the solution, given
; the formula 5 + (2 * (m - 4))
(definec game-length (s :state) :nat
  :ic (is-valid-start s)
  (+ 5 (* 2 (- (caar s) 4))))
; game-length checks
(check= (game-length (list '(5 5) 'left '(0 0) nil)) 7)
(check= (game-length (list '(27 27) 'left '(0 0) nil)) 51)

(def-const *last* (list (move 0 4 'right)
                          (move 1 0 'left)
                          (move 4 0 'right)
                          (move 1 0 'left)
                          (move 2 0 'right)))

; checks if a list of moves follows the previously
; mentioned pattern property (see intro to this section)
(definec valid-game-lom (lom :lom) :boolean
  (cond
   ((last-moves lom) t)
   ((consp lom) (and (equal (first lom) (move 2 2 'right))
                     (equal (second lom) (move 1 1 'left))
                     (valid-game-lom (rest (rest lom)))))
   (t nil)))
; valid-game-lom checks
(check= (valid-game-lom (cons (move 1 1 'left) *last*)) nil)
(check= (valid-game-lom (alg '(10 10) 'left '(0 0))) t)

; given a valid start state, are our expected properties
; satisfied?
(test? (implies (and (statep s)
                     (is-valid-start s))
                (let ((moves (alg-help (first s) 
                                       (second s) 
                                       (third s))))
                  (and (= (length moves)
                          (game-length s))
                       (valid-game-lom moves)))))

;;;;;;;;;;;;;;; Simulator functions ;;;;;;;;;;;;

#|
In this section, we test our algorithm for correctness
by creating a simulator function, which takes a list
of moves and the fields of a state and outputs a new
state according to the moves specified. We expect that,
given a valid start state, running simulate on said state
with the list of moves produced by alg-help will produce
a valid game end state (defined below).
|#

; checks if a move is valid, given the conditions of
; the current game state
(definec valid-move (m :move lc :count b :side rc :count) :boolean
  (if (equal b 'left)
    ; if boat is on left side, move must be toward
    ; right side and should not take more monsters
    ; and munchkins than there are on left side
    (and (move-rightp m)
         (>= (first lc) (second m))
         (>= (second lc) (fifth m)))
    ; vice versa for right side
    (and (move-leftp m)
         (>= (first rc) (second m))
         (>= (second rc) (fifth m)))))
; valid-move checks
(check= (valid-move (move 2 2 'right) '(5 5) 'left '(0 0)) t)
(check= (valid-move (move 2 2 'right) '(5 5) 'right '(0 0)) nil)
(check= (valid-move (move 6 2 'right) '(5 5) 'left '(0 0)) nil)

; simulates a single move in the game
(definecd simulate-move (m :move lc :count b :side rc :count f :boolean) :state
  (declare (ignorable b))
  (if f
    ; if error flag triggered, return invalid state
    (list lc b rc f)
    (cond 
     ;; if boat is on right side, move is toward left,
     ;; and move is valid, update state
     ((and (move-rightp m)
           (equal b 'left)
           (valid-move m lc b rc)) (list 
                                    (list (- (first lc) (second m))
                                          (- (second lc) (fifth m)))
                                    'right
                                    (list (+ (first rc) (second m))
                                          (+ (second rc) (fifth m)))
                                    nil))
     ;; if boat is on left side, move is toward right,
     ;; and move is valid, update state
     ((and (move-leftp m)
           (equal b 'right)
           (valid-move m lc b rc)) (list
                                    (list (+ (first lc) (second m))
                                          (+ (second lc) (fifth m)))
                                    'left
                                    (list (- (first rc) (second m))
                                          (- (second rc) (fifth m)))
                                    nil))
     ;; if invalid move, return state with flag triggered
     (t (list lc b rc t)))))
; simulate-move checks
(check= (simulate-move (move 2 2 'right) '(5 5) 'left '(0 0) t)
        (list '(5 5) 'left '(0 0) t))
(check= (simulate-move (move 6 2 'right) '(5 5) 'left '(0 0) nil)
        (list '(5 5) 'left '(0 0) t))
(check= (simulate-move (move 2 2 'right) '(5 5) 'left '(0 0) nil)
        (list '(3 3) 'right '(2 2) nil))

; simulate the execution of a list of moves in a game
(defun simulate (lom lc b rc f)
  (cond
   ; if the list of moves is empty, return the 
   ; current state
   ((endp lom) (list lc b rc f))
   ; if the error flag is triggered, return the
   ; current invalid state
   (f (list lc b rc f))
   ; simulate the first move in the list, and
   ; then recurse with the updated fields
   (t (let ((res (simulate-move (first lom) lc b rc f)))
            (simulate (rest lom)
                (first res)
                (second res)
                (third res)
                (fourth res))))))
; simulate checks
(check= (simulate (alg '(5 5) 'left '(0 0))
                  '(5 5) 'left '(0 0) t)
        (list '(5 5) 'left '(0 0) t))
(check= (simulate (alg '(5 5) 'left '(0 0))
                  '(5 5) 'left '(0 0) nil)
        (list '(0 0) 'right '(5 5) nil))
(check= (simulate (list (move 2 2 'right) (move 1 1 'left))
                  '(10 10) 'left '(0 0) nil)
        (list '(9 9) 'left '(1 1) nil))

; check if given state is a valid end to the game
(definec is-valid-end (s :state) :boolean
       ; boat is on the right side
  (and (equal (second s) 'right)
       ; right side has an equal amount of
       ; monsters and munchkins
       (= (first (third s)) (second (third s)))
       ; left side has 0 monsters and 0 munchkins
       (= (first (first s)) 0)
       (= (second (first s)) 0)
       ; error flag is not triggered
       (not (fourth s))))
; is-valid-end checks
(check= (is-valid-end (list '(5 5) 'left '(0 0) nil)) nil)
(check= (is-valid-end (list '(0 0) 'left '(5 5) nil)) nil)
(check= (is-valid-end (list '(0 0) 'right '(5 5) t)) nil)
(check= (is-valid-end (list '(1 0) 'right '(5 5) nil)) nil)
(check= (is-valid-end (list '(0 0) 'right '(5 5) nil)) t)

; given a valid start state, is the end state
; produced by simulating moves given by the algorithm
; a valid end state?
(test? (implies (and (statep s)
                     (is-valid-start s))
                 (is-valid-end (simulate (alg-help (first s) 
                                                   (second s) 
                                                   (third s))
                                         (first s)
                                         (second s)
                                         (third s)
                                         (fourth s)))))#|ACL2s-ToDo-Line|#
