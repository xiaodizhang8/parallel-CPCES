
(define (domain dispose)

   (:requirements :strips :typing)
   (:types pos obj)
   (:predicates (adj ?i ?j - pos) (located ?i - pos) (holding ?o - obj) (obj_at ?o - obj ?i - pos)
                (trash_at ?x - pos) (disposed ?o - obj))
   (:action move
      :parameters (?i - pos ?j - pos )
      :precondition (and (adj ?i ?j) (located ?i))
      :effect (and (not (located ?i)) (located ?j)))
   (:action pickup
      :parameters (?o - obj ?i - pos)
      :precondition (located ?i)
      :effect (when (obj_at ?o ?i) (and (holding ?o) (not (obj_at ?o ?i)))))
   (:action drop
      :parameters (?o - obj ?i - pos )
      :precondition (and (located ?i) (trash_at ?i))
      :effect (when (holding ?o) (and (not (holding ?o)) (disposed ?o)))))

