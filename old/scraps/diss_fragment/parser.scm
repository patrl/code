; -*- mode: Scheme -*-

; Code by Chris Barker and Chung-chieh (Ken) Shan.  
; Reference parser for Shan and Barker, Explaining crossover and superiority 
; as left to right evaluation, to appear in Linguistics and Philosophy.
; 2002-2005.

; usage: compile with bigloo like this:
; 	bigloo -static-bigloo -Obench -o parse parser.scm
; then do:
;       ./parse grammar-file

; Portability issues: works with bigloo compiler with the following
; module declaration.  Also works with guile (much slower...)
; Other schemes (MIT, PLT) don't treat \ as a normal character.
; (Easy to change \ to b/ and \\ to b// in the parser.scm and grammar.)

; Stuff for the bigloo compiler:
(module parser (eval (export-all)) (main start))
(define (start argv) (if (pair? argv) (load (cadr argv))))

; Stuff that some schemes may need
; (define (filter pred lst)
;   (cond ((null? lst) '())
;         ((pred (car lst)) 
;            (cons (car lst) (filter pred (cdr lst))))
;         (else (filter pred (cdr lst)))))
; (define (any fn l)(if (null? l) #f (or (fn (car l)) (any fn (cdr l)))))
; (define (get-problem x) (load x))

;=============================================================================
; Variables under user control

(define grammar '())
(define slash '/)
(define backslash '\)
(define filter-cats '(1))
(define max-edges 10000)
(define max-depth 6)
(define max-continuation-level 2)
(define max-lift-level 3)
(define debug? #f)
(define display-derivation? #f)

;=============================================================================
; Parsing variables

(define input "")       ; string to be parsed
(define chart '())      ; list of well-formed expressions
(define agenda '())     ; list of edges waiting to be added to the chart
(define secondary-agenda '())
(define rules '())
(define edge-count 0)
(define subcharts-starting-at '())
(define subcharts-ending-at '())

;=============================================================================
;  Data structure
;
;     data structure for edge (an edge is a well-formed expression)
;
(define signature car)
  (define expr caar)
  (define cat cadar)
  (define (proof-net edge) (car (cddar edge)))
  (define (start-point edge) (car (cdddr (signature edge))))
  (define (end-point edge) (cadr (cdddr (signature edge))))
(define semantics cadr)
(define history caddr) ; proofnet; build in compare
(define daughters cadddr)
(define (pattern e) (car (cddddr e)))

(define (rule? e) (or (symbol? (expr e))
		      (zero? (string-length (expr e)))))

; A symbol is a variable just in case it is a number (test with "number?")

(define (depth cat)
  (if (not (pair? cat))
      0
      (+ 1 (apply max (map depth cat)))))

(define (continuation-level cat)
  (cond ((not (pair? cat)) 0)
	((eq? '// (cadr cat))
	 ((lambda (tail)
	    (if (even? tail) tail (+ 1 tail)))
	  (continuation-level (car cat))))
	((eq? '\\ (cadr cat))
	 ((lambda (tail)
	    (if (even? tail) (+ 1 tail) tail))
	  (continuation-level (car cat))))
	(else 
	 (apply max (map continuation-level cat)))
	))

(define (lift-level cat)
  (cond ((not (pair? cat)) 0)
	((eq? '\ (cadr cat))
	 ((lambda (tail)
	    (if (even? tail) tail (+ 1 tail)))
	  (lift-level (car cat))))
	((eq? '/ (cadr cat))
	 ((lambda (tail)
	    (if (even? tail) (+ 1 tail) tail))
	  (lift-level (car cat))))
	(else ;(eq? '==> (cadr cat))
	 (apply max (map lift-level cat)))
	))


; if fresh?, map variables onto fresh symbols; if (not fresh?),
; map variables onto variables corresponding to low numbers, i.e., 0, 1  
(define (normalize f fresh?)
  (let ((i 0) (g '()))
    (let traverse ((f f))
      (cond ((number? f)
	     (if (assq f g)
		 (cdr (assq f g))
		 (begin
		   (set! i (+ 1 i))
		   (set! g (cons (cons f
				       (if fresh?
					   (string->number
					    (symbol->string
					     (gensym "")))
					   i))
				 g))
		   (traverse f))))
	    ((not (pair? f)) f)
	    (else (cons (traverse (car f))
			(traverse (cdr f))))))))

(define (schedule edge)
  (and (>= max-edges (length chart))
       (>= max-depth (depth (cat edge)))
       (>= (* 2 max-continuation-level) (continuation-level (cat edge)))
       (>= (* 2 max-lift-level) (lift-level (cat edge)))
       (set! agenda (append agenda (list edge)))
       ))

(define (add-edge raw-edge)

  ; this let stores a pre-computed fresh pattern to use in comparisons later
  (let ((edge (append raw-edge (list (normalize (cat raw-edge) 'fresh)))))

    (if (and (not (assoc (signature edge) chart))
	     (> max-edges edge-count))
	(begin
	  (set! edge-count (+ 1 edge-count))
	  (debug "Adding:    " edge)
	  
	  (if (filter-edge edge filter-cats)
	      (begin (newline)(display "-------------------")(newline)
		     (display "edge      : ")
		     (display (length chart))
		     (display " ")
		     (display-edge edge)))
	  
	  (set! chart (cons edge chart))
	  
	  (if (rule? edge)
	      (set! rules (cons edge rules))
	      (begin
		(vector-set! subcharts-starting-at
			     (start-point edge)
			     (cons edge (vector-ref subcharts-starting-at
						    (start-point edge))))
		(vector-set! subcharts-ending-at
			     (end-point edge)
			     (cons edge (vector-ref subcharts-ending-at
						    (end-point edge))))))
	  
	  (if (rule? edge)
	      (for-each (lambda (old)
			  (compare edge old)
			  (if (not (eq? edge old))
			      (compare old edge)))
			chart)
	      (begin
		(for-each (lambda (old)
			    (compare old edge)
			    (compare edge old))
			  rules)
		(for-each (lambda (old) (compare old edge))
			  (vector-ref subcharts-ending-at (start-point edge)))
		(for-each (lambda (old) (compare edge old))
			  (vector-ref subcharts-starting-at (end-point edge)))
		)))
	)))

(define (combine-strings l r)
  (cond ((and (rule? l) (rule? r)) "")
	((rule? l) (expr r))
	((rule? r) (expr l))
	(else (string-append (expr l) " " (expr r)))))

(define (compare l r)
  (compare-slash l r)
  (compare-backslash l r))

(define (compare-slash l r)
  (let ((pattern (pattern l)))
    (and pattern
	 (pair? pattern)
	 (= 3 (length pattern))
         (eq? slash (cadr pattern))
	 (pre-unify (caddr pattern) (cat r))
	 (unify (caddr pattern) (cat r) '())
	 (let ((history
		((lambda (u) (if u (cdr u) u))
		 (unification
		  (normalize
		   `(,(car (history l)) 1 (,(history l) 2))
		   'fresh)
		  (normalize
		   `((1 ,slash ,(car (history r))) 1 (2 ,(history r)))
		   'fresh)))))
	   (schedule (list (list (combine-strings l r)
				 (normalize (car (unification
						    pattern
						    (list 0 slash (cat r))))
					    #f)
				 (normal-yield history)
				 (start-point (if (rule? l) r l))
				 (end-point (if (rule? r) l r))
				 )
			   (reduce (list (semantics l)(semantics r)))
			   history
			   (list l r)
			   ))))))

(define (compare-backslash l r)
  (let ((pattern (pattern r)))
    (and pattern
	 (pair? pattern)
	 (= 3 (length pattern))
         (eq? backslash (cadr pattern))
	 (pre-unify (car pattern) (cat l))
	 (unify (car pattern) (cat l) '())
	 (let ((history
		((lambda (u) (if u (cdr u) u))
		 (unification
		  (normalize
		   `((,(car (history l)) ,backslash 1) 1 (,(history l) 2))
		   'fresh)
		  (normalize `
		   (,(car (history r)) 1 (2 ,(history r)))
		   'fresh)))))
	   (schedule (list (list (combine-strings l r)
				 (normalize (caddr (unification
						  (list (cat l) backslash 0)
						  pattern))
					    #f)
				 (normal-yield history)
				 (start-point (if (rule? l) r l))
				 (end-point (if (rule? r) l r))
				 )
			   (reduce (list (semantics r)(semantics l)))
			   history
			   (list l r)
			   ))))))

(define (process-words input position)
  (and
   (not (null? input))
   (begin 
     (for-each
      (lambda (entry)
	(if (equal? (expr entry) (symbol->string (car input)))
	    (add-edge (list (list (symbol->string (car input))
				  (cat entry)
				  (normalize (list (lex2net (cat entry))
						   (cons 'lex (expr entry)))
					     #f)
				  position
				  (+ 1 position))
			    (semantics entry)
			    (normalize (list (lex2net (cat entry))
					     (cons 'lex (expr entry)))
				       'fresh)
			    '()))))
      grammar)
     (process-words (cdr input) (+ 1 position)))))

(define (process-rules)
  (map (lambda (entry)
	 (and (rule? entry) 
	      (add-edge
	       (list (append (car entry) 
			     (list
			      (normalize (list (lex2net 
						(if (eq? 'E (expr entry))
						    '(1 / (1 // (2 \\ 2)))
						    (cat entry)))
					       (cons 'rule (expr entry)))
					 #f)
			      'R
			      'R))
		     (semantics entry)
		     (normalize (list (lex2net 
				       (if (eq? 'E (expr entry))
					   '(1 / (1 // (2 \\ 2)))
					   (cat entry)))
				      (cons 'rule (expr entry)))
				'fresh)
		     '()))))
       grammar))

(define (complete-chart)
  (if (not (null? agenda))
      (begin (let ((new (car agenda)))
	       (set! agenda (cdr agenda))
	       (add-edge new))
	     (complete-chart))))

(define (parse string)
  (display (list "Processing: " string))(newline)
  (set! edge-count 0)
  (set! chart '())
  (set! rules '())
  (set! agenda '())
  (set! input string)
  (set! subcharts-starting-at
	(make-vector (+ 1 (length input)) '()))
  (set! subcharts-ending-at
	(make-vector (+ 1 (length input)) '()))
  (set! filter-cats (map (lambda (raw) (normalize raw 'fresh)) filter-cats))
  (process-words input 0)
  (process-rules)
  (complete-chart)
  (display (length chart))
  (display " edges -- Done parsing.")(newline)
)

(define literals '(e t))

(define (lex2net tree)
  (cond ((null? tree) tree)
	((pair? tree) (cons (lex2net (car tree))
			    (lex2net (cdr tree))))
	((member tree literals) (cons (string->number
				       (symbol->string (gensym "")))
				      tree))
	(else tree)))

(define (normal-yield tree) (normalize (cons (car tree) (yield tree)) #f))

(define (yield tree)
  (cond ((and (pair? tree)
	      (pair? (cdr tree))
	      (pair? (cadr tree))
	      (eq? 'lex (caadr tree)))
	 (list (list (cdadr tree) (car tree))))
	((pair? tree)
	 (append (yield (car tree))(yield (cdr tree))))
	(else '())))

(define (filter-edge edge cats)
  (and (pair? cats)
;       (equal? input (expr edge))
       (and (not (rule? edge))
	    (= 0 (start-point edge))
	    (= (length input) (end-point edge)))
       (or (unify (cat edge) (car cats) '())
	   (filter-edge edge (cdr cats)))))

(define (derivation-concise history)
  (if (pair? (caadr history))
      (list (derivation-concise (caadr history))
            (derivation-concise (cadadr history)))
      (cdr (cadr history))))

(define (display-tree edge depth)
  (if edge
      (begin
	(newline)(display depth)(display depth)
	(if (equal? "" (expr edge))
	    (display "RULE")
	    (display (expr edge)))
	(display " ")
	(display (cat edge))
	(display " = ")
	(display (semantics edge))
	(if (not (null? (cadddr edge))) ; should be (if (has-daughters? edge)
	    (begin
	      (display-tree (car (daughters edge)) (string-append " " depth))
	      (display-tree (cadr (daughters edge)) (string-append " " depth))
	      )))))

(define (display-edge e)
  (display (expr e))
  (display "	")
  (display (list (start-point e) (end-point e)))
  (display "	")
  (display (cat e))
  (display " ")
  (newline)
  (display "semantics : ")
  (display (semantics e))
  (newline)
  (display "proofnet  : ")
  (display (proof-net e))
  (newline)
  (display "derivation: ")
  (display (derivation-concise (history e)))
  (newline)
  (if display-derivation?
      (begin (display-tree e "")
	     (newline)))
  )

(define (get-cats f)
  (cond ((null? f) '())
	((pair? f) (list (car (check f))
			 (get-cats (car f))
			 (get-cats (cadr f))))
	(else (list (car (check f)) f))))


; only works for / throughout
(define (check f)
  (cond ((null? f) f)
	((pair? f)
	 (list (normalize (car (unification
				(normalize (car (check (car f))) 'fresh)
				(list 0 slash (car (check (cadr f))))))
			  #f)
	       (normalize (reduce (list (cadr (check (car f)))
					(cadr (check (cadr f)))))
			  #f)))
	(else
	 (list (cadaar (filter (lambda (e) (equal? (caar e) f)) grammar))
	       (cadr (car (filter (lambda (e) (equal? (caar e) f)) grammar))
		     )))))

(define (debug tag e)
  (and debug? (display tag) (if e (display-edge e) (newline))))


;=============================================================================
; Unification algorithm 
;
; Based on Arthur Nunes-Harwitt, http://www.ccs.neu.edu/home/arthur/unif.html
; unify returns environment (list of pairs) if successful or #f otherwise.
;
(define (unify l r env)
  (and env
       (cond ((eq? l r) env)
	     ((assq l env) (unify (cdr (assq l env)) r env))
	     ((assq r env) (unify l (cdr (assq r env)) env))
	     ((number? l) (and
			   ; comment next line if don't need occurs-check
			   (occurs-check l (unifier r env))
			   `((,l . ,r) . ,env)))
	     ((number? r) (and
			   ; comment next line if don't need occurs-check
			   (occurs-check r (unifier l env))
			   `((,r . ,l) . ,env)))
	     ((and (pair? l)(pair? r))
	      (unify (cdr l) (cdr r) (unify (car l) (car r) env)))
	     (else #f))))

; Correctly rejects most unification attempts.
; Purely for efficiency; does as much checking 
; as it can without building new structure.
;
(define (pre-unify l r)
  (or (eq? l r)
      (number? l)
      (number? r)
      (and (pair? l)
	   (pair? r)
	   (pre-unify (car l)(car r))
	   (pre-unify (cdr l)(cdr r)))))

(define (unifier x env)
  (if (pair? x)
      (cons (unifier (car x) env)(unifier (cdr x) env))
      (let ((binding (assq x env)))
	(if binding (unifier (cdr binding) env) x))))

(define (unification l r)
  (letrec ((solution (unify l r '())))
    (if solution (unifier l solution) #f)))

; returns #t if var does not occur in tree
(define (occurs-check var tree)
  (if (eq? var tree) #f
      (or (not (pair? tree))
	  (and (occurs-check var (car tree))
	       (occurs-check var (cdr tree))))))
	      
;----------------------------------------------------------------------------
; Reduce, written by Ken Shan based on Plotkin 1975

; (reduce f) reduces the lambda-term f.
(define reduce (lambda (f)
  (letrec ((r (lambda (f g) (cond
	      ; variable: substitute or leave alone
	      ((not (pair? f))
	       (cond ((assq f g) => cdr)
		     (else f)))
	      ; beta-redex: reduce function body with revised assignment
	      ((and (pair? (car f))
		    (= 2 (length f))
		    (or (eq? 'lambda (caar f)) (eq? '^ (caar f))))
	       (let ((g2 (cons (cons (cadar f) (r (cadr f) g))
			       (delq (cadar f) g))))
		 (r (caddar f) g2)))
	      ; binding construct: reduce while worrying about variable capture
	      ((binding f)
	       (let* ((g2 (delq (cadr f) g))
		      (y2 (fresh (cadr f) (cddr f) g2))
		      (g3 (if y2 (cons (cons (cadr f) y2) g2) g2)))
	         (cons (car f) (r (cdr f) g3))))
	      ; everything else: reduce recursively
	      (#t (map (lambda (x) (r x g)) f))))))
     ; reduce until the lambda-term stabilizes
     (let ((f2 (r f '())))
          (if (equal? f f2) f (reduce f2))))))

; (binding f) is true iff the lambda-term f is a binding construct:
; one of lambda (aka ^), exists, and forall.
(define binding (lambda (f)
  (and (= 3 (length f))
       (or (eq? 'lambda (car f))
           (eq? '^ (car f))
           (eq? 'exists (car f))
           (eq? 'forall (car f))))))

; (free var f) is true iff the variable var appears free
; in the lambda-term f.
(define free (lambda (var f)
  (cond ((not (pair? f))
	 (eq? var f))
	((binding f)
	 (and (not (equal? var (cadr f)))
	      (free var (caddr f))))
	(else
	 (or (free var (car f))
	     (free var (cdr f)))))))

; (delq obj alist) removes from the association list alist the first entry
; whose key is eq? to obj, if any.  In fact, the way we invoke delq above
; guarantees that there is at most one such entry.
(define delq (lambda (obj alist)
  (if (assq obj alist) (delq-aux obj alist) alist)))
(define delq-aux (lambda (obj alist)
  (if (eq? obj (caar alist))
      (cdr alist)
      (cons (car alist) (delq obj (cdr alist))))))

; (fresh y f g) is invoked by reduce.  It produces a renaming y2 of the
; variable y such that, for every entry (x . m) in the assignment g,
; either x does not appear free in f, or y2 does not appear free in m.
; If y already satisfies the above criterion, then #f is produced
; Otherwise, the renaming y2 returned does not appear free in f.
(define fresh (lambda (y f g)
  ; filter g, keeping only entries (x . m) such that x appears free in f
  (let ((g2 (filter (lambda (a) (free (car a) f)) g)))
    ; consider each successive renaming y2 of y
    (let loop ((i 0))
      (let ((y2 (if (zero? i)
		    y
		    (string->symbol (string-append
				    (substring (symbol->string y) 0 1)
				    (number->string i))))))
        (if (or (and (> i 0) (free y2 f))
	        (any (lambda (a) (free y2 (cdr a))) g2))
	    (loop (+ i 1))
	    y2))))))
