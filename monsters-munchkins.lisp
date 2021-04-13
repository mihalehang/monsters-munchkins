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
(defdata boat (list nat side))#|ACL2s-ToDo-Line|#


;; DONT FORGET TO WRITE CONTRACTS YALL ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






;; Traditional Algorithm

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
           ;; if 0 munchkins on right side and boat is on left
           ;; side, there should also be 0 monsters on right side
           (implies (and (equal (second b) 'left)
                         (zp (second rc)))
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
            

;
(definec (lc :count b :boat rc :count) :tl
  (

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



