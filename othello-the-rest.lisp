;; ==================================
;;  CMPU-365, Spring 2019
;;  FILE:  othello-the-rest.lisp
;; ==================================
;;  The *rest* of the OTHELLO implementation!

;;  Defines the following METHODS that ARE used by MCTS
;; ---------------------------------------------------------
;;     DO-MOVE!       -- destructively does a move
;;     LEGAL-MOVES    -- returns a vector of legal moves
;;     GAME-OVER?     -- returns T or NIL
;;     DEFAULT-POLICY -- does random moves until game over

;;  Defines the following METHODS & MACROS that are NOT used by MCTS
;; -------------------------------------------------------------------------
;;     IS-LEGAL?          -- tells whether given move is legal
;;     HAS-LEGAL-MOVE?    -- tells whether current player has at least one legal move
;;     MUST-PASS? (macro) -- tells whether current player must pass
;;     RANDOM-MOVE        -- used by DO-RANDOM-MOVE!
;;     DO-RANDOM-MOVE!    -- used by DEFAULT-POLICY


;;  The following constants are used by IS-LEGAL?
;; -------------------------------------------------------------------

;;  *DIRNS*
;; --------------------------------------------------------
;;  An 8-by-2 array representing the 8 different directions
;;  one could travel from a given square on the board.

(defconstant *dirns* (make-array '(8 2)
				 :initial-contents
				 '((1 1) (1 0) (1 -1)
				   (0 1) (0 -1)
				   (-1 1) (-1 0) (-1 -1))))

;;  For a move at (ROW COL) to be legal, there needs to be a
;;  streak of tokens emanating from (ROW COL) in one of the 8
;;  possible directions (but not including (ROW COL) itself)
;;  that consists of one-or-more of YOUR tokens, followed by
;;  one of MY tokens.  If the first token encountered in some
;;  direction is one of YOUR tokens, then from there we need
;;  zero or more of YOUR tokens followed by one of MY tokens.
;;  Thus, as we look along each of the 8 directions, the STATUS
;;  is initially *NEED-YOU+-ME*, but then may become *NEED-YOU*-ME*.

;;  "Status" used while searching a streak of tokens
;; ---------------------------------------------------------
;;  *NEED-YOU+-ME*:  Need one or more of YOUR tokens, followed by one of MY tokens
;;  *NEED-YOU*-ME*:  Need zero or more of YOUR tokens, followed by one of MY tokens

(defconstant *need-you+-me* 0)
(defconstant *need-you*-me* 1)

(defconstant *fail* 2)
(defconstant *done* 3)

;;  IS-LEGAL?
;; -----------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           PLAYER, *black* or *white*
;;           ROW, COL, integers
;;  OUTPUT:  T if this is a legal move for PLAYER

(defmethod is-legal?
    ((game othello) row col)
  (let ((bored (othello-board game))
	(player (othello-whose-turn game))
	;; TOKEN, DR, DC, STATUS, R, C:  local variables used
	;;   during the DOTIMES, below
	token dr dc status r c)

    ;; This function shouldn't be called on a PASS move
    (assert (not (is-pass? (list row col))))

    ;; If (ROW COL) is not *blank*, then can't put a token there
    (when (not (eq (aref bored row col) *blank*))
      (return-from is-legal? nil))

    ;; For each of the 8 directions emanating from (ROW COL)...
    (dotimes (dirn 8)
      ;; (DR,DC) = direction of travel
      ;; STATUS is initially *NEED-YOU+-ME*
      ;; (R,C) starts out at (ROW,COL), but will be incremented
      ;;   using (DR,DC) as we move outward along some direction
      (setf dr (aref *dirns* dirn 0)
	    dc (aref *dirns* dirn 1)
	    status *need-you+-me*
	    r row
	    c col)
      ;; WHILE we may still discover a streak in the current direction
      ;; that would make (ROW COL) a legal move...
      (while (not (= status *fail*))
	;; Move (R C) one unit in the direction (DR,DC)
	(incf r dr)
	(incf c dc)
	(cond
	 ;; Case 1:  (R C) is off the board!
	 ((off-board? r c)
	  ;; This direction of travel cannot confirm that (ROW COL) is
	  ;; a legal move
	  (setf status *fail*))
	 ;; Case 2:  (R C) is on the board
	 (t
	  ;; TOKEN:  the token at position (R C)
	  (setf token (aref bored r c))
	  (cond
	   ;; Case 2a:  Found a blank, or one of my tokens
	   ;;           before seeing one of yours
	   ((or (eq token *blank*)
		(and (eq token player)
		     (= status *need-you+-me*)))
	    ;; This direction has failed, so must look elsewhere
	    (setf status *fail*))
	   ;; Case 2b:  Found one of my tokens after
	   ;;           having already seen one or more of yours
	   ((eq token player)
	    ;; That's the end of a flipping streak!
	    ;; Thus (ROW COL) is a legal move. So return from
	    ;;  IS-LEGAL? immediately!! Break out of the DOTIMES
	    (return-from is-legal? t))
	   ;; Case 3:  Found one of your tokens
	   (t
	    ;; keep looking in the same direction
	    (setf status *need-you*-me*))))))
      ;; After the WHILE
      )
    ;; After the DOTIMES:  If we got here, none of the 8 directions
    ;;   was able to confirm that (ROW COL) is legal.  Therefore...
    nil))

;;  DO-MOVE!
;; -------------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           CHECK-LEGAL?, T or NIL
;;           ROW, COL, two integers (between 0 and 7)
;;  OUTPUT:  The modified GAME
;;  SIDE EFFECT:  Destructively modifies GAME by doing the specified move.
;;    Note:  If CHECK-LEGAL? is T, then it only does the move if it
;;           passes the IS-LEGAL? check.

(defmethod do-move!
    ((game othello) check-legal? row col)

  ;; Check whether the move is legal, if desired.
  (when (and check-legal?
	     (not (is-legal? game row col)))
    (format t "Not gonna do an illegal move!~%")
    (return-from do-move! nil))

  ;; For a PASS move, only need to toggle whose-turn
  (when (is-pass? (list row col))
    (toggle-player! game)
    (return-from do-move! game))

  ;; For any other move...
  (let ((bored (othello-board game))
	(player (othello-whose-turn game))
	token dr dc status r c
	(potential-flips (make-array '(8 2)))
	num-potential-flips
	)
    ;; Place token on the board at (ROW COL)
    (place-token game bored player row col)

    ;; For each of 8 possible directions, accumulate
    ;; potential flippings.  This code is similar to what's
    ;; in IS-LEGAL? except that we accumulate tokens to flip.

    (dotimes (dirn 8)
      (setf dr (aref *dirns* dirn 0)
	    dc (aref *dirns* dirn 1)
	    status *need-you+-me*
	    r row
	    c col
	    num-potential-flips 0)
      (while (not (= status *done*))
	(incf r dr)
	(incf c dc)
	(cond
	 ;; Case 0:  Whoops!
	 ((off-board? r c)
	  ;; No more flippings in this direction
	  (setf status *done*))
	 ;; Case 1:  (R C) is still on the board
	 (t
	  (setf token (aref bored r c))
	  (cond
	   ;; Case 1a:  Found a blank, or one of my tokens
	   ;;           before seeing one of yours
	   ((or (eq token *blank*)
		(and (eq token player)
		     (= status *need-you+-me*)))
	    ;; Look along a different direction
	    (setf status *done*))
	   ;; Case 1b:  Found one of my tokens after
	   ;;           having already seen one or more of yours
	   ((eq token player)
	    ;; That's the end of a flipping streak
	    ;; DO each potential flip!
	    (dotimes (i num-potential-flips)
	      (let ((r (aref potential-flips i 0))
		    (c (aref potential-flips i 1)))
		(flip-token game bored player r c)))
	    (setf status *done*)
	    )
	   ;; Case 1c:  Found one of your tokens
	   (t
	    ;; keep looking along this direction (accumulating a potential flip)
	    (setf (aref potential-flips num-potential-flips 0) r)
	    (setf (aref potential-flips num-potential-flips 1) c)
	    (incf num-potential-flips)
	    (setf status *need-you*-me*))))))
      ;; After the WHILE
      )
    ;; After the DOTIMES
    (toggle-player! game)
    (decf (othello-num-open game))
    game))


;;  LEGAL-MOVES
;; -------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT:  A VECTOR of the legal moves available to the current player.
;;  Note:  If no "legal" moves, then returns a vector containing the *pass* move.

(defmethod legal-moves
    ((game othello))
  (let ((moves nil)
	(num-moves 0))
    ;; Just look at every square, seeing if it's legal
    (dotimes (r 8)
      (dotimes (c 8)
	(when (is-legal? game r c)
	  (push (list r c) moves)
	  (incf num-moves))))
    (if (> num-moves 0)
	(make-array num-moves :initial-contents moves)
      ;; if no legal moves, then player must *pass*
      (vector *pass*))))

;;  HAS-LEGAL-MOVE?
;; ----------------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           PLR, either *BLACK* or *WHITE*
;;  OUTPUT:  T if PLR has at least one legal move (i.e., doesn't need to pass)
;;           NIL if PLR must pass

(defmethod has-legal-move?
    ((game othello))
  ;; Check each square on the board until you find one that's legal
  (dotimes (r 8)
    (dotimes (c 8)
      (when (is-legal? game r c)
	(return-from has-legal-move? t))))
  ;; if got here, no legal moves
  nil)


;;  MUST-PASS?
;; -------------------------------------------------------
;;  INPUTS:  GAME, an OTHELLO struct
;;           PLR, either *BLACK* or *WHITE*
;;  OUTPUT:  T, if PLR's only legal move is to pass;
;;           NIL otherwise.
;; --------------------------------------------------------------------
;; NOTE:  MUST-PASS? can be MUCH MORE EFFICIENT by STOPPING legal-moves
;;        as soon as it finds just ONE move...

(defmacro must-pass?
    (game plr)
  `(let ((turn (othello-whose-turn ,game)))
     (cond
      ;; Case 1:  It's PLR's turn
      ((eq ,plr turn)
       (not (has-legal-move? ,game)))
       ;; Case 2:  It is NOT PLR's turn
      (t
       ;; Set it to be PLR's turn
       (toggle-player! ,game)
       (let ((answer (not (has-legal-move? ,game))))
	 (toggle-player! ,game)
	 answer)))))

;;  GAME-OVER?
;; --------------------------------------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT:  T if the game is over (i.e., either no open slots in the
;;    game board, or the only move available to *both* players is *pass*).

(defmethod game-over?
    ((game othello))
  (or (zerop (othello-num-open game))
      (and (must-pass? game *black*)
	   (must-pass? game *white*))))

;;  DEFAULT-POLICY
;; ---------------------------------------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT: The result (from black's perspective) of playing out the
;;    current game using randomly selected moves.  The amount of the
;;    win/loss is reported by the SQUARE-ROOT of the absolute difference
;;    in the number of tokens for the two players.  For example, if the
;;    game ends with WHITE having 25 tokens and BLACK having 31 tokens,
;;    then black wins by 6 tokens, and the output is approximately 2.45.

(defmethod default-policy
    ((game othello))
  ;; Do random moves until the game is over
  (while (not (game-over? game))
    (do-random-move! game))
  ;; Then count up the tokens for each player and compute the score
  (let* ((counts (count-tokens game))
	 (whites (first counts))
	 (blacks (second counts))
	 (diff (- blacks whites)))
    ;; The winner's score is the square root of the difference
    ;; of the number of tokens.  Black win is positive, White negative.
    (cond
     ;; Case 1:  BLACK won
     ((< diff 0)
      (- 0 (sqrt (abs diff))))
     ;; Case 2:  WHITE won
     ((> diff 0)
      (sqrt diff))
     ;; Case 3:  A tie!
     (t
      0))))

(defmethod eval-func
  ((game othello))
 	(let*
    ((counts (count-tokens game))
   	 (whites (first counts))
   	 (blacks (second counts))
   	 (diff (- blacks whites)))
    ;; The winner's score is the square root of the difference
    ;; of the number of tokens.  Black win is positive, White negative.
    (cond
      ;; Case 1:  BLACK won
      ((< diff 0)
       (- 0 (sqrt (abs diff))))
      ;; Case 2:  WHITE won
      ((> diff 0)
       (sqrt diff))
      ;; Case 3:  A tie!
      (t
       0))))

;;  RANDOM-MOVE
;; ------------------------------------------
;;  INPUT:  GAME, an OTHELLO struct
;;  OUTPUT:  One of the legal moves available to the current
;;   player, chosen randomly.

(defmethod random-move
    ((game othello))
  (let* ((moves (legal-moves game)))
    (svref moves (random (length moves)))))

;;  DO-RANDOM-MOVE!
;; ------------------------------------------------
;;  INPUT:   GAME, an OTHELLO struct
;;  OUTPUT:  The modified game
;;  SIDE EFFECT:  Destructively modifies GAME by doing one of the
;;   legal moves available to the current player, chosen randomly.

(defmethod do-random-move!
    ((game othello))
  (let ((move (random-move game)))
    (apply #'do-move! game nil move)))
