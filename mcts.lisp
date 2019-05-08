;; ========================================
;;  CMPU-365, Spring 2019
;;  Monte Carlo Tree Search
;; ========================================
;;  An implementation of the MCTS algorithm

;;  Defines the following functions used by MCTS algorithm
;; ----------------------------------------------------------
;;     GET-ROOT-NODE
;;     NEW-MC-TREE
;;     INSERT-NEW-NODE
;;     SIM-TREE
;;     SIM-DEFAULT
;;     BACKUP
;;     UCT-SEARCH
;;     SELECT-MOVE

;;  In addition, for testing, defines:  COMPETE

;;  The MCTS functions call the following DOMAIN-DEPENDENT
;;  functions that are defined in "othello-starter.lisp":
;; ------------------------------------------------------------------
;;     COPY-GAME               -- creates a copy of the given othello game board
;;     MAKE-HASH-KEY-FROM-GAME -- returns list of the form (WHITE-PCS BLACK-PCS WHOSE-TURN)
;;     WHOSE-TURN              -- returns *BLACK* or *WHITE*

;;  The MCTS functions call the following DOMAIN-DEPENDENT
;;  functions that are defined in "othello-the-rest.lisp":
;; ------------------------------------------------------------------
;;     DO-MOVE!        --  does a move (destructively modifies game struct)
;;     LEGAL-MOVES     --  returns VECTOR of legal moves
;;     GAME-OVER?      --  returns T or NIL
;;     DEFAULT-POLICY  --  returns random legal move


;;  Note:  If a player has no legal moves, but the game isn't over, then that
;;         player *must* pass...


;;  MC-NODE struct -- a node in the MCTS tree
;; ----------------------------------------------------------------------------
;;  KEY:          a hash-table key (compact rep'n of current state of game)
;;  WHOSE-TURN:   *BLACK* or *WHITE*
;;  NUM-VISITS:   the number of times this state has been visited
;;  VECK-MOVES:   a VECTOR of the legal moves from this state
;;  VECK-VISITS:  a VECTOR recording the number of times each legal move
;;                   has been visited during MCTS
;;  VECK-SCORES:  a VECTOR recording the average scores for the legal
;;                   moves visited during MCTS

(defstruct mc-node
  key
  whose-turn
  (num-visits 0)
  veck-moves
  veck-visits
  veck-scores
  amaf-visits
  amaf-scores
  )

;;  MC-TREE struct -- the MCTS tree
;; -------------------------------------------------------------
;;  HASHY:     a hash-table whose entries are (key,value), where
;;               key = compact repn of state, value = mc-node
;;  ROOT-KEY:  the hash-table key for the root node of the mcts tree

(defstruct mc-tree
  (hashy (make-hash-table :test #'equal))
  root-key)

;;  GET-ROOT-NODE
;; ------------------------------------------------------
;;  INPUT:   TREE, a MCTS struct
;;  OUTPUT:  The MC-NODE corresponding to the root of the TREE

(defun get-root-node
    (tree)
  (gethash (mc-tree-root-key tree) (mc-tree-hashy tree)))

;; -------------------------------------------------
;;  Easiest to define the necessary functions
;;  in the following order
;; -------------------------------------------------

;;  NEW-MC-TREE
;; ---------------------------------
;;  INPUT:   GAME, a game struct
;;  OUTPUT:  A new MC tree whose root state is derived
;;           from GAME.

(defun new-mc-tree
    (game)
  (make-mc-tree :root-key (make-hash-key-from-game game)))


;;  INSERT-NEW-NODE
;; -----------------------------------------
;;  INPUTS:  GAME, a game struct
;;           TREE, an MC-TREE struct
;;           KEY, a hash-key representing the state of the game
;;  OUTPUT:  The newly created and inserted node
;;  SIDE EFFECT:  Inserts a new node into TREE using KEY.

(defun insert-new-node
  (game tree key)
  (let* ((moves (legal-moves game))
       	 (num-moves (length moves))
       	 (nodey (make-mc-node
              		 :key key
              		 :veck-moves moves
              		 :veck-visits (make-array num-moves :initial-element 0)
              		 :veck-scores (make-array num-moves :initial-element 0)
                   :amaf-visits (make-array num-moves :initial-element 0)
                   :amaf-scores (make-array num-moves :initial-element 0)
              		 :whose-turn (whose-turn game))))
    ;; insert nodey into tree
    (setf (gethash key (mc-tree-hashy tree)) nodey)
    ;; return the node
    nodey))

;;  SELECT-MOVE
;; ------------------------------------------
;;  INPUTS:  NODEY, an MC-NODE struct
;;           C, exploitation-exploration constant
;;  OUTPUT:  The INDEX of the selected move into the moves vector

(defun select-move
  (nodey k)
  (format t "starting selectmv!~%")
  (let*
    ((player (mc-node-whose-turn nodey))
   	 (moves (mc-node-veck-moves nodey))
   	 (num-moves (length moves)))
    (cond
      ;; No legal moves!
      ((= num-moves 0)
       ;; signal failure
       nil)
      ;; Only one legal move
      ((= num-moves 1)
       ;; return it
       0)
      ;; Two or more moves
      (t
       (let*
         ((n (mc-node-num-visits nodey))
          (beta (sqrt (/ k (+ (* n 3) k))))
          (mc-scoress (mc-node-veck-scores nodey))
          (amaf-scoress (mc-node-amaf-scores nodey))
     	    (best-move-so-far nil)
     	    (best-score-so-far (if (eq player *black*)
                               *neg-inf*
                               *pos-inf*)))
         (dotimes
          (i num-moves)
     	    ;; Fetch weighted score for this move
     	    (let*
            ((mc-score (svref mc-scoress i))
             (amaf-score (svref amaf-scoress i))
             (weighted-score (+ (* (- 1 beta) mc-score) (* beta amaf-score))))
     	      ;; When SCORE is better than best-score-so-far...
     	      (when
              (or
               (and
                (eq player *black*)
                (> weighted-score best-score-so-far))
               (and
                (eq player *white*)
                (< weighted-score best-score-so-far)))
              ;; Update best-score/move-so-far
              (setf best-score-so-far weighted-score)
              (setf best-move-so-far i))))
        	;; Return best-move-so-far or (if NIL) a random move
         (format t "selectmv success!~%")
         (if best-move-so-far
           best-move-so-far
           (random num-moves)))))))


;;  SIM-TREE
;; --------------------------------------
;;  INPUTS:  GAME, a game struct
;;           TREE, an MC-TREE struct
;;           C, the exploration/exploitation constant
;;  OUTPUT:  A list of the form (state0 move0 state1 move1 ... statek movek)
;;    where each state_i is a key into the hashtable, and each move_i
;;    is an index into the MOVES vector of the node assoc with state_i.

(defun sim-tree
  (game tree k)
  (let (;; KEY-MOVE-ACC:  accumulator of KEYs and MOVEs
       	(key-move-acc nil)
       	(hashy (mc-tree-hashy tree)))
    (while (not (game-over? game))
      (let* (;; KEY:  Hash key for current state of game
       	     (key (make-hash-key-from-game game))
       	     ;; NODEY:  The MC-NODE corresponding to KEY (or NIL if not in tree)
       	     (nodey (gethash key hashy)))
       	;; Case 1:  When key not yet in tree...
       	(when (null nodey)
       	  ;; Create new node and insert it into tree
       	  (setf nodey (insert-new-node game tree key))
       	  (let* ((mv-index (select-move nodey k))
                 (move-veck (mc-node-veck-moves nodey))
                 (move (svref move-veck mv-index)))
       	    (apply #'do-move! game nil move)
       	    (push key key-move-acc)
       	    (push mv-index key-move-acc)
       	    ;; return the accumulator prepended with selected MOVE
       	    ;; and KEY for current state
            (format t "tree success!~%")
       	    (return-from sim-tree (reverse key-move-acc))))

       	;; Case 2:  Key already in tree!
       	(let* ((mv-index (select-move nodey k))
       	       (move-veck (mc-node-veck-moves nodey))
       	       (move (svref move-veck mv-index)))
       	  (apply #'do-move! game nil move)
       	  (push key key-move-acc)
       	  (push mv-index key-move-acc))))

    ;; After the WHILE... return the accumulated key/move list
    (format t "tree success!~%")
    (reverse key-move-acc)))

;;  SIM-DEFAULT
;; ----------------------------------------------
;;  INPUT:   GAME, a game struct
;;  OUTPUT:  The result of following the game's default policy
;;             (domain-dependent method)

(defun sim-default
  (game)
  (let ((move-acc nil))
    (while (not (game-over? game))
      (let ((move (random-move game)))
        (apply #'do-move! game nil move)
        (push move move-acc)))
    (push (eval-func game) move-acc)
    (format t "default success!~%")
    (reverse move-acc)))

;;  BACKUP
;; ---------------------------------------------------
;;  INPUTS:  HASHY, the hash-table for the MCTS
;;           KEY-MOVE-ACC, the accumulated list of KEYs and MOVEs
;;              from a simulation run
;;           RESULT, the result (from black's perspective) of the
;;              recently played out simulation
;;  OUTPUT:  doesn't matter
;;  SIDE EFFECT:  Updates the relevant nodes in the MC-TREE/HASHY

(defun merge-moves
  (key-move-acc move-acc hashy)
  (let
    ((simtree-moves nil))
    (dotimes
     (i (/ (length key-move-acc) 2))
     (push
      ;; move
      (svref
       ;; vector of moves
       (mc-node-veck-moves
        ;; node
        (gethash
         ;; key
         (nth (* i 2) key-move-acc)
         ;; tree (hash table)
         hashy))
       ;; move-index
       (nth (+ (* i 2) 1) key-move-acc))
      ;; accumulator
      simtree-moves))
    (setf move-acc (append (reverse simtree-moves) move-acc))))

(defun sublist-member
  (item listy till)
  (let ((i 0))
    (while (<= i (- till 2))
      (when
        (equal
         item
         (nth i listy))
        (return-from sublist-member t))
      (incf i 2))
    nil))

(defun array-member
  (item arr)
  (dotimes
   (i (length arr))
   (when
     (equal
      item
      (svref arr i))
     (return-from array-member i)))
  nil)

(defun backup
  (hashy key-move-acc move-acc)
  (merge-moves key-move-acc move-acc hashy)
  (while key-move-acc
    (let*
      ((result (first (last move-acc)))
       (key (pop key-move-acc))
   	   (nodey (gethash key hashy))
   	   (mv-index (pop key-move-acc))
       (veck-moves (mc-node-veck-moves nodey))
       (mc-visits (mc-node-veck-visits nodey))
       (mc-scores (mc-node-veck-scores nodey))
       (amaf-visits (mc-node-amaf-visits nodey))
       (amaf-scores (mc-node-amaf-scores nodey)))
      ;; increment MC stats
      (incf (mc-node-num-visits nodey))
      (incf (svref mc-visits mv-index))
      (incf (svref mc-scores mv-index)
       	    (/ (- result (svref mc-scores mv-index))
       	       (svref mc-visits mv-index)))
      (let ((i 0))
        ;; the last entry is result
        (while (< i (- (length move-acc) 1))
          (let*
            ((mv (nth i move-acc))
             ;; is move_i legal at current state?
             (legal-p (array-member mv veck-moves)))
            (when
              (and
               ;; move-i is legal at current state
               legal-p
               ;; move_i is not within the seen moves
               (not (sublist-member mv move-acc i)))
              ;; updates AMAF
              (incf (svref amaf-visits legal-p))
              (incf (svref amaf-scores legal-p)
               	    (/ (- result (svref amaf-scores legal-p))
               	       (svref amaf-visits legal-p)))))
          (incf i 2))
        (format t "backup success!~%")
        (setf move-acc (rest move-acc))))))

;;  UCT-SEARCH
;; ---------------------------------
;;  INPUTS:  ORIG-GAME, a game struct
;;           NUM-SIMS, a positive integer
;;           C, the exploration/exploitation parameter
;;  OUTPUT:  Best move from that state determined by
;;             doing *NUM-SIMS* simulations of MCTS.

(defparameter *verbose* t) ;; a global parameter used to ensure/suppress printing of stats

(defun mc-rave
  (orig-game num-sims k)
  ;; Want to use COPY of GAME struct for simulations...
  ;; That way, can reset game struct before each simulation...
  (let* ((tree (new-mc-tree orig-game))
       	 (hashy (mc-tree-hashy tree))
       	 ;;(player (whose-turn orig-game))
       	 )
    (dotimes (i num-sims)
             (let* (;; Work with a COPY of the original game struct
              	     (game (copy-game orig-game))
              	     ;; Phase 1:  SIM-TREE Destructively modifies game
              	     (key-move-acc (sim-tree game tree k))
              	     ;; Phase 2:  SIM-DEFAULT returns result
              	     (move-acc (sim-default game)))
              	;; Finally, backup the results
              	(backup hashy key-move-acc move-acc)))
    ;; Select the best move (using c = 0 because we are not exploring anymore)
    (let* ((rootie (get-root-node tree))
       	   (mv-index (select-move rootie k))
       	   (move (svref (mc-node-veck-moves rootie) mv-index))
       	   (scores (mc-node-veck-scores rootie))
       	   (score (svref scores mv-index)))
      (format t ".")
      (when *verbose*
       	;; Display some stats along with the best move
       	(format t "Best score: ~5,3F score veck: " score)
       	(dotimes (i (length scores))
              	  (format t "~5,3F, " (svref scores i)))
       	(format t "~%")
       	(format t "Visits veck: ")
       	(dotimes (i (length scores))
              	  (format t "~A " (svref (mc-node-veck-visits rootie) i)))
       	(format t "~%"))
      ;; Output the move
      move)))

;;  COMPETE
;; --------------------------------------------------
;;  INPUTS:  BLACK-NUM-SIMS, the number of simulations for each of black's moves
;;           BLACK-C, the exploration/exploitation constant used by black
;;           WHITE-NUM-SIMS, the number of simulations for each of white's moves
;;           WHITE-C, the exploration/exploitation constant used by white
;;  OUTPUT:  Don't care
;;  SIDE EFFECT:  Displays the entire game using UCT-SEARCH to compute best moves
;;    for both players according to the specified parameters.

(defun compete
    (black-num-sims black-k white-num-sims white-k)
  (setf *verbose* t)
  (let ((g (new-othello)))
    (while (not (game-over? g))
      (cond
       ((eq (whose-turn g) *black*)
	(format t "BLACK'S TURN!~%")
	(format t "~A~%"
		(apply #'do-move! g nil (mc-rave g black-num-sims black-k))))
       (t
	(format t "WHITE'S TURN!~%")
	(format t "~A~%"
		(apply #'do-move! g nil (mc-rave g white-num-sims white-k))))))))


;;  COMPETE-NO-PRINTING
;; --------------------------------------------------
;;  Same as COMPETE, but only shows the end result

(defun compete-no-printing
    (black-num-sims black-k white-num-sims white-k)
  (setf *verbose* nil)
  (let ((g (new-othello)))
    (while (not (game-over? g))
      (cond
       ((eq (whose-turn g) *black*)
	(format t "B ")
	(apply #'do-move! g nil (mc-rave g black-num-sims black-k)))
       (t
	(format t "W ")
	(apply #'do-move! g nil (mc-rave g white-num-sims white-k)))))
    (format t "~%~A~%" g)))
