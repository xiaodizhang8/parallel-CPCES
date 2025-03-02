(define (domain uts)
   (:types node)
   (:predicates (visited ?x - node) (edge ?x ?y - node) (located ?x - node) (started))

   (:action starting
     :parameters (?x - node)
     :precondition ()
     :effect (when (located ?x) (and (started) (visited ?x)))
   )
   (:action travel
     :parameters (?x ?y - node)
     :precondition (started)
     :effect (when (and (located ?x) (edge ?x ?y)) (and (visited ?y) (located ?y) (not (located ?x))))
   )
)

