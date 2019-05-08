;; ===============================================
;;  CMPU-365, Spring 2019
;;  FILE:  othello-macros.lisp
;; ===============================================
;;  Some constants and macros that are useful for implementing OTHELLO!

;;   Defines the following HELPER MACROS, which are used
;;   only by other macros defined in this file.
;; --------------------------------------------------------------------
;;   POSN->ROW, POSN->COL (used by PLACE-TOKEN-AT-POSN)
;;   ROW-COL->POSN (used by PLACE-TOKEN, FLIP-TOKEN)
;;   IF-BLACK-TURN (used by PRINT-OTHELLO)
;;   IF-BLACK (used by TOGGLE-PLAYER!, PLACE-TOKEN, FLIP-TOKEN)
;;   PLACE-TOKEN-AT-POSN (used by NEW-OTHELLO)

;;   Defines the following additional MACROS, which are used
;;   by IS-LEGAL? and DO-MOVE! (defined in "othello-starter.lisp"
;;   and "othello-the-rest.lisp", respectively)
;; --------------------------------------------------------------------
;;
;;   TOGGLE-PLAYER! (used by DO-MOVE!)
;;   PLACE-TOKEN (used by DO-MOVE!)
;;   FLIP-TOKEN (used by DO-MOVE!)
;;   IS-PASS? (used by IS-LEGAL?, DO-MOVE!)
;;   OFF-BOARD? (used by IS-LEGAL?, DO-MOVE!)


;;  Some useful constants
;; -----------------------------------

;;  Colors of tokens/blank spaces

(defconstant *black* -1)
(defconstant *white* 1)
(defconstant *blank* 0)

;;  How tokens of each color are displayed

(defconstant *black-show* 'B)
(defconstant *white-show* 'W)
(defconstant *blank-show* '_)

;;  Plus/Minus Infinity

(defparameter *pos-inf*  10000000)
(defparameter *neg-inf* -10000000)

;;  The PASS move is represented thusly:

(defconstant *pass* '(nil nil))

;;  A POSN is just a number from 0 to 63, that refers to one of the
;;  squares on the 8-by-8 othello game board.  The following macros
;;  convert between the POSN and ROW/COL representations.

;;  POSN->ROW
;; ---------------------------------------------------------------------
;;  INPUT:   POSN (i.e., an integer from 0 to 63)
;;  OUTPUT:  The corresponding ROW (an integer from 0 to 7)

(defmacro posn->row (posn) `(floor ,posn 8))

;;  POSN->COL
;; ---------------------------------------------------------------
;;  INPUT:   POSN (i.e., an integer from 0 to 63)
;;  OUTPUT:  The corresponding COLUMN (an integer from 0 to 7)

(defmacro posn->col (posn) `(mod ,posn 8))

;;  ROW-COL->POSN
;; ------------------------------------------
;;  INPUTS:  ROW, COL, two integers each between 0 and 7
;;  OUTPUT:  The corresponding POSN (an integer between 0 and 63)

(defmacro row-col->posn (row col) `(+ (* 8 ,row) ,col))

;;  IF-BLACK-TURN
;; -------------------------------------------------------
;;  INPUTS:  G, an OTHELLO struct
;;           THEN, ELSE, any two Lisp expressions
;;  OUTPUT:  If it's black's turn, then evaluate THEN;
;;           Otherwise, evaluate ELSE.

(defmacro if-black-turn (g then else)
  `(if (eq (othello-whose-turn ,g) ,*black*)
       ,then ,else))

;;  IF-BLACK
;; --------------------------------------------------------
;;  INPUTS:  PLR, either *BLACK* or *WHITE*
;;           THEN, ELSE, any Lisp expressions
;;  OUTPUT:  If PLR is *BLACK* then evaluate THEN;
;;           Otherwise, evaluate ELSE.

(defmacro if-black (plr then else)
  `(if (eq ,plr ,*black*) ,then ,else))

;;  TOGGLE-PLAYER!
;; ---------------------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT: The player whose turn it now is (either *BLACK* or *WHITE*)
;;  SIDE EFFECT:  Destructively modifies the game to toggle whose turn it is.

(defmacro toggle-player! (game)
  `(setf (othello-whose-turn ,game)
     (if-black (othello-whose-turn ,game) ,*white* ,*black*)))

;;  PLACE-TOKEN-AT-POSN
;; --------------------------------------------------------------
;;  INPUTS:  BOARD, an 8-by-8 array
;;           TOKEN, either *BLACK* or *WHITE*
;;           POSN, an integer from 0 to 63
;;  OUTPUT:  Doesn't matter
;;  SIDE EFFECT:  Destructively modifies BOARD by inserting TOKEN
;;                at the position determined by POSN

(defmacro place-token-at-posn
    (board token posn)
  `(setf (aref ,board (posn->row ,posn) (posn->col ,posn)) ,token))

;;  PLACE-TOKEN
;; -------------------------------------------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           BORED, an 8-by-8 array
;;           PLR, either *BLACK* or *WHITE*
;;           ROW, COL, integers between 0 and 7
;;  OUTPUT:  Doesn't matter
;;  SIDE EFFECT:  Places TOKEN on BORED at specified ROW/COL.
;;    Also updates the 64-bit vector for the appropriate player
;;    (see the STATE struct)

(defmacro place-token
    (game bored plr row col)
  `(progn (setf (aref ,bored ,row ,col) ,plr)
	  (if-black ,plr (incf (othello-black-pieces ,game)
			       (ash 1 (row-col->posn ,row ,col)))
		    (incf (othello-white-pieces ,game)
			  (ash 1 (row-col->posn ,row ,col))))))

;;  FLIP-TOKEN
;; ------------------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           BOARD, an 8-by-8 array
;;           PLR, either *BLACK* or *WHITE*
;;           R,C, two integers between 0 and 7
;;  OUTPUT:  Irrelevant
;;  SIDE EFFECT:  Destructively modifies game by flipping the
;;    token at the position R=ROW/C=COLUMN.  Also adjusts the
;;    64-bit vectors for the two players appropriately.

(defmacro flip-token
    (game board plr r c)
  `(progn (setf (aref ,board ,r ,c) ,plr)
	  (if-black ,plr
		    (let ((power (ash 1 (row-col->posn ,r ,c))))
		      (incf (othello-black-pieces ,game) power)
		      (decf (othello-white-pieces ,game) power))
		    (let ((power (ash 1 (row-col->posn ,r ,c))))
		      (incf (othello-white-pieces ,game) power)
		      (decf (othello-black-pieces ,game) power)))))

;;  IS-PASS?
;; ---------------------------------------------
;;  INPUT:   MOVE, a list of the form (ROW COL)
;;  OUTPUT:  T if ROW = NIL; otherwise NIL.
;; ---------------------------------------------
;;  NOTE:  A *pass* move is represented as (NIL NIL)
;;         Any other move is (ROW COL) where ROW and COL are integers

(defmacro is-pass?
    (move)
  `(eq (first ,move) nil))

;;  MUST-PASS? moved to OTHELLO.LISP (more efficient version)

;;  OFF-BOARD?
;; ------------------------------------------
;;  INPUTS:  ROW, COL, two integers
;;  OUTPUT:  T if (ROW,COL) does not specify a legal position
;;              in an 8-by-8 array; NIL otherwise.

(defmacro off-board?
    (row col)
  `(or (< ,row 0)
       (< ,col 0)
       (> ,row 7)
       (> ,col 7)))
