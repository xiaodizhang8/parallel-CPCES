(define (problem coins_3_8_2_879)
  (:domain coins)
  (:objects e0 e1 - elevator f0 f1 f2 - floor p0 p1 p2 p3 p4 p5 p6 p7 - pos c0 c1 c2 c3 c4 c5 - coin)
  (:init (dec_f f1 f0) (dec_f f2 f1) (dec_p p1 p0) (dec_p p2 p1) (dec_p p3 p2) (dec_p p4 p3) (dec_p p5 p4) (dec_p p6 p5) (dec_p p7 p6) (shaft e0 p2) (located f0 p0)(shaft e1 p3) 

(in e0 f0)
(in e1 f0) 

(cpt (coin-at c0 f0 p0) 0.125) (cpt  (coin-at c0 f0 p1) 0.125) (cpt  (coin-at c0 f0 p2) 0.125) (cpt  (coin-at c0 f0 p3) 0.125) (cpt  (coin-at c0 f0 p4) 0.125) (cpt  (coin-at c0 f0 p5) 0.125) (cpt  (coin-at c0 f0 p6) 0.125) (cpt  (coin-at c0 f0 p7) 0.125) 
  (multi (coin-at c0 f0 p0) (coin-at c0 f0 p1) (coin-at c0 f0 p2) (coin-at c0 f0 p3) (coin-at c0 f0 p4) (coin-at c0 f0 p5) (coin-at c0 f0 p6) (coin-at c0 f0 p7) ) 

(cpt (coin-at c1 f2 p0) 0.125) (cpt  (coin-at c1 f2 p1) 0.125) (cpt  (coin-at c1 f2 p2) 0.125) (cpt  (coin-at c1 f2 p3) 0.125) (cpt  (coin-at c1 f2 p4) 0.125) (cpt  (coin-at c1 f2 p5) 0.125) (cpt  (coin-at c1 f2 p6) 0.125) (cpt  (coin-at c1 f2 p7) 0.125) 
  (multi (coin-at c1 f2 p0) (coin-at c1 f2 p1) (coin-at c1 f2 p2) (coin-at c1 f2 p3) (coin-at c1 f2 p4) (coin-at c1 f2 p5) (coin-at c1 f2 p6) (coin-at c1 f2 p7) ) 

(cpt (coin-at c2 f1 p0) 0.125) (cpt  (coin-at c2 f1 p1) 0.125) (cpt  (coin-at c2 f1 p2) 0.125) (cpt  (coin-at c2 f1 p3) 0.125) (cpt  (coin-at c2 f1 p4) 0.125) (cpt  (coin-at c2 f1 p5) 0.125) (cpt  (coin-at c2 f1 p6) 0.125) (cpt  (coin-at c2 f1 p7) 0.125) 
  (multi (coin-at c2 f1 p0) (coin-at c2 f1 p1) (coin-at c2 f1 p2) (coin-at c2 f1 p3) (coin-at c2 f1 p4) (coin-at c2 f1 p5) (coin-at c2 f1 p6) (coin-at c2 f1 p7) ) 

(cpt (coin-at c3 f0 p0) 0.125) (cpt  (coin-at c3 f0 p1) 0.125) (cpt  (coin-at c3 f0 p2) 0.125) (cpt  (coin-at c3 f0 p3) 0.125) (cpt  (coin-at c3 f0 p4) 0.125) (cpt  (coin-at c3 f0 p5) 0.125) (cpt  (coin-at c3 f0 p6) 0.125) (cpt  (coin-at c3 f0 p7) 0.125) 
  (multi (coin-at c3 f0 p0) (coin-at c3 f0 p1) (coin-at c3 f0 p2) (coin-at c3 f0 p3) (coin-at c3 f0 p4) (coin-at c3 f0 p5) (coin-at c3 f0 p6) (coin-at c3 f0 p7) ) 

(cpt (coin-at c4 f2 p0) 0.125) (cpt  (coin-at c4 f2 p1) 0.125) (cpt  (coin-at c4 f2 p2) 0.125) (cpt  (coin-at c4 f2 p3) 0.125) (cpt  (coin-at c4 f2 p4) 0.125) (cpt  (coin-at c4 f2 p5) 0.125) (cpt  (coin-at c4 f2 p6) 0.125) (cpt  (coin-at c4 f2 p7) 0.125) 
  (multi (coin-at c4 f2 p0) (coin-at c4 f2 p1) (coin-at c4 f2 p2) (coin-at c4 f2 p3) (coin-at c4 f2 p4) (coin-at c4 f2 p5) (coin-at c4 f2 p6) (coin-at c4 f2 p7) ) 

(cpt (coin-at c5 f0 p0) 0.125) (cpt  (coin-at c5 f0 p1) 0.125) (cpt  (coin-at c5 f0 p2) 0.125) (cpt  (coin-at c5 f0 p3) 0.125) (cpt  (coin-at c5 f0 p4) 0.125) (cpt  (coin-at c5 f0 p5) 0.125) (cpt  (coin-at c5 f0 p6) 0.125) (cpt  (coin-at c5 f0 p7) 0.125)
  (multi (coin-at c5 f0 p0) (coin-at c5 f0 p1) (coin-at c5 f0 p2) (coin-at c5 f0 p3) (coin-at c5 f0 p4) (coin-at c5 f0 p5) (coin-at c5 f0 p6) (coin-at c5 f0 p7) ) 



  
  )
  (:goal 0.9
  (and (have c0) (have c1) (have c2) (have c3) (have c4) (have c5) ))
)
