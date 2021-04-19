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
;; Termination proof of Traditional Algorithm

(set-termination-method :measure)
(set-well-founded-relation n<)
(set-defunc-typed-undef nil)
(set-defunc-generalize-contract-thm nil)
(set-gag-mode nil)

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

(set-ignore-ok t)

;; Measure function

(definec alg-measure (lc :count b :side rc :count) :nat ;; alg-help vs alg
  (if (and (equal b 'left) (> (first lc) 4))
    (1+ (first lc)) 0))#|ACL2s-ToDo-Line|#


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

;; Termination Proof
Conjecture alg-terminates:
(implies (and (countp lc) 
              (sidep b)
              (count rc))
         (< (alg-measure (list (1+ (first lc)) (second lc)) b rc)
            (alg-measure lc b rc)))

Context:
C1. (countp lc)
C2. (sidep b)
C3. (countp rc)

Goal:
(< (alg-measure (list (1- (first lc)) (second lc)) b rc)
            (alg-measure lc b rc))

Proof:


QED