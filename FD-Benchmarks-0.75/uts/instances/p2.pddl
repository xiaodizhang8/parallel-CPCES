(define (problem k4)  (:domain uts)  (:objects n1 n2 n3 n4 - node)  (:init                           (edge n1 n2)              (edge n1 n3)              (edge n1 n4)              (edge n2 n1)              (edge n2 n3)              (edge n2 n4)              (edge n3 n1)              (edge n3 n2)              (edge n3 n4)              (edge n4 n1)              (edge n4 n2)              (edge n4 n3)    
(cpt (located n1) 0.25)              
(cpt (located n2) 0.25)              
(cpt (located n3) 0.25)              
(cpt (located n4) 0.25)           
(multi (located n1) (located n2) (located n3) (located n4))                            


)  

(:goal 0.75
(and (visited n1) (visited n2) (visited n3) (visited n4))))