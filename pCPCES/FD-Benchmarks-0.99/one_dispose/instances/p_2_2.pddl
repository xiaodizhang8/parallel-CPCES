(define (problem dispose_2_2)(:domain dispose) (:objects     o1    o2 - obj     p1_1    p1_2    p2_1    p2_2 - pos     )   (:init      (handempty)     (not (holding o1))     (not (holding o2))     (located p1_1)     (trash_at p1_1)          (adj p1_1 p2_1)     (adj p2_1 p1_1)     (adj p1_2 p2_2)     (adj p2_2 p1_2)     (adj p1_1 p1_2)     (adj p1_2 p1_1)     (adj p2_1 p2_2)     (adj p2_2 p2_1)     

(cpt (obj_at o1 p1_1) 0.25)(cpt (obj_at o1 p1_2) 0.25)(cpt (obj_at o1 p2_1) 0.25)(cpt (obj_at o1 p2_2) 0.25)
(multi        (obj_at o1 p1_1)        (obj_at o1 p1_2)        (obj_at o1 p2_1)        (obj_at o1 p2_2)     )     

(cpt (obj_at o2 p1_1) 0.25)(cpt (obj_at o2 p1_2) 0.25)(cpt (obj_at o2 p2_1) 0.25)(cpt (obj_at o2 p2_2) 0.25)
(multi        (obj_at o2 p1_1)        (obj_at o2 p1_2)        (obj_at o2 p2_1)        (obj_at o2 p2_2)     )        



)    

(:goal 0.99
(and     (disposed o1)    (disposed o2))))