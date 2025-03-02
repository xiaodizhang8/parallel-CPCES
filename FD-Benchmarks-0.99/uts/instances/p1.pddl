(define (problem k2)  (:domain uts)  (:objects n1 n2 - node)  (:init                    (edge n1 n2)           (edge n2 n1)   
(cpt (located n1) 0.5)       (cpt (located n2) 0.5)         
(multi (located n1) (located n2))               
 

)  
(:goal 0.99
(and (visited n1) (visited n2))))