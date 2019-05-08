;; ========================================
;;  CMPU-365, Spring 2019
;;  FILE:  othello-starter.lisp
;; ========================================

;;  Defines the following functions
;; ------------------------------------------------------
;;     PRINT-STATE
;;     COPY-ARRAY
;;     PRINT-OTHELLO
;;     COUNT-TOKENS
;;     NEW-OTHELLO

;;  Defines the following METHODS that ARE used by MCTS
;; ---------------------------------------------------------
;;     COPY-GAME
;;     MAKE-HASH-KEY-FROM-GAME

;;  Defines the following METHODS that are NOT used by MCTS
;; ------------------------------------------------------------
;;     RANDOM-MOVE
;;     DO-RANDOM-MOVE!

;; The following constant facilitates the display of 64-bit numbers
;; when printing out the othello game board

(defconstant *2^64* (ash 1 64))

;;  The OTHELLO struct
;; --------------------------------------------------------
;;  Note:  WHITE-PIECES & BLACK-PIECES are 64-bit integers.
;;           Each bit in these 64-bit integers corresponds to one of the 64 slots
;;           in the 8-by-8 game board.  (See othello-macros.lisp for macros that
;;           convert between the POSN and ROW/COL representations.)  If the ith
;;           bit is a 1, then that player has a token in the ith POSN; otherwise, no.

(defstruct (othello (:print-function print-othello))
  ;; BOARD:  an 8-by-8 array of *white*, *black* or *blank*
  (board (make-array '(8 8) :initial-element *blank*))
  ;; WHOSE-TURN:  either *BLACK* or *WHITE*
  whose-turn
  ;; NUM-OPEN:  the number of open spaces on the BOARD (always <= 60)
  num-open
  ;; WHITE-PIECES/BLACK-PIECES:  64-bit integers (as described above)
  white-pieces
  black-pieces
  )

;;  WHOSE-TURN
;; -----------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT: The player whose turn it is (*black* or *white*)

(defmethod whose-turn
    ((game othello))
  (othello-whose-turn game))


;;  COPY-ARRAY
;; -------------------------------------------------
;;  INPUT:   HARRY, a 2-dimensional array
;;  OUTPUT:  A copy of HARRY

(defun copy-array
    (harry)
  (let* ((dims (array-dimensions harry))
	 (kopy (make-array dims)))
    (dotimes (r (first dims))
      (dotimes (c (second dims))
	(setf (aref kopy r c) (aref harry r c))))
    kopy))

;;  COPY-GAME
;; ------------------------------------------
;;  INPUT:   GAME, an OTHELLO struct
;;  OUTPUT:  A copy of GAME

(defmethod copy-game
    ((game othello))
  (make-othello :board (copy-array (othello-board game))
		:whose-turn (othello-whose-turn game)
		:num-open (othello-num-open game)
		:white-pieces (othello-white-pieces game)
		:black-pieces (othello-black-pieces game)))

;;  PRINT-OTHELLO
;; --------------------------------------------------
;;  INPUTS:  G, an OTHELLO struct
;;           STR, output stream (or T)
;;           DEPTH, ignored
;;  OUTPUT:  None
;;  SIDE EFFECT:  Displays the OTHELLO game

(defun print-othello
    (g str d)
  (declare (ignore d))
  (let ((bored (othello-board g)))
    (format str "~% | 0 1 2 3 4 5 6 7~%")
    (format str "------------------~%")
    (dotimes (r 8)
      (format str "~A| " r)
      (dotimes (c 8)
	(let ((token (aref bored r c)))
	  (format str "~A " (cond ((eq token *black*) *black-show*)
				  ((eq token *white*) *white-show*)
				  (t *blank-show*)))))
      (format str "~%"))
    (format str "~%")
    (format str "                   It is ~A's turn!~%"
	    (if-black-turn g *black-show* *white-show*))
    (format str "  white: ~,'0,'_,8:b~%" (+ *2^64* (othello-white-pieces g)))
    (format str "  black: ~,'0,'_,8:b~%" (+ *2^64* (othello-black-pieces g)))
    (let ((counts (count-tokens g)))
      (format str "  num-whites: ~A, num-blacks: ~A~%" (first counts) (second counts)))
    ))

;;  COUNT-TOKENS
;; ----------------------------------------
;;  INPUT:   G, an OTHELLO struct
;;  OUTPUT:  A list of the form (WHITES BLACKS) indicating the number of
;;           tokens by the two players that are currently on the board

(defun count-tokens (g)
  (let ((whites 0)
	(blacks 0)
	(bored (othello-board g))
	token)
    (dotimes (r 8)
      (dotimes (c 8)
	(setf token (aref bored r c))
	(cond ((eq token *black*) (incf blacks))
	      ((eq token *white*) (incf whites)))))
    (list whites blacks)))

;;  NEW-OTHELLO
;; --------------------------------------
;;  INPUTS:  None
;;  OUTPUT:  An OTHELLO struct representing a new game

(defun new-othello
    ()
  (let* ((game (make-othello :whose-turn *black*
			     :num-open 60
			     :white-pieces (+ (ash 1 27) (ash 1 36))
			     :black-pieces (+ (ash 1 28) (ash 1 35))))
	 (bored (othello-board game)))
    (place-token-at-posn bored *white* 27)
    (place-token-at-posn bored *white* 36)
    (place-token-at-posn bored *black* 28)
    (place-token-at-posn bored *black* 35)
    game))


;;  MAKE-HASH-KEY-FROM-GAME
;; --------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT:  A list of the form (WHITE-PIECES BLACK-PIECES WHOSE-TURN)
;;    where the contents are as described in the STATE struct

(defmethod make-hash-key-from-game
    ((game othello))
  (list (othello-white-pieces game)
	(othello-black-pieces game)
	(othello-whose-turn game)))
