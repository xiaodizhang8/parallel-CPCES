
(define (domain dispose)

   (:requirements :strips)
   (:types pos obj)
  
   (:predicates (adj ?i ?j - pos) (located ?i - pos) (holding ?o - obj) (obj_at ?o - obj ?i - pos)
                (trash_at ?x - pos) (disposed ?o - obj) (handempty))
   (:action move
      :parameters (?i - pos ?j - pos )
      :precondition (and (adj ?i ?j) (located ?i))
      :effect (and (not (located ?i)) (located ?j)))
   (:action pickup
      :parameters (?p - pos ?o - obj)
      :precondition (located ?p) 
      :effect (and 
                 (when (and (handempty) (obj_at ?o ?p))
                       (and (not (handempty)) (holding ?o) (not (obj_at ?o ?p))))
              )
   )
   (:action putdown
      :parameters (?p - pos ?o - obj)
      :precondition (and (located ?p) (trash_at ?p))
      :effect (and 
                 (when (holding ?o)
                       (and (handempty) (not (holding ?o)) (disposed ?o)))
                       )
   )
)

