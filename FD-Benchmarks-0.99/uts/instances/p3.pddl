(define (problem k6)  (:domain uts)  (:objects n1 n2 n3 n4 n5 n6 - node)  (:init                        (edge n1 n2)              (edge n1 n3)              (edge n1 n4)              (edge n1 n5)              (edge n1 n6)              (edge n2 n1)              (edge n2 n3)              (edge n2 n4)              (edge n2 n5)              (edge n2 n6)              (edge n3 n1)              (edge n3 n2)              (edge n3 n4)              (edge n3 n5)              (edge n3 n6)              (edge n4 n1)              (edge n4 n2)              (edge n4 n3)              (edge n4 n5)              (edge n4 n6)              (edge n5 n1)              (edge n5 n2)              (edge n5 n3)              (edge n5 n4)              (edge n5 n6)              (edge n6 n1)              (edge n6 n2)              (edge n6 n3)              (edge n6 n4)              (edge n6 n5)          
(cpt (located n1)  0.16667)              
(cpt (located n2)  0.16667)              
(cpt (located n3)  0.16667)              
(cpt (located n4)  0.16667)              
(cpt (located n5)  0.16667)              
(cpt (located n6)  0.16667)    
(multi (located n1) (located n2) (located n3) (located n4) (located n5) (located n6))                       
           
)  

(:goal 0.99
(and (visited n1) (visited n2) (visited n3) (visited n4) (visited n5) (visited n6))))