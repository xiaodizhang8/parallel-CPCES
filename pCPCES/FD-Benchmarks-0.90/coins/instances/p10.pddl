(define (problem coins_2_4_2_7523)
  (:domain coins)
  (:objects e0 e1 - elevator f0 f1 - floor p0 p1 p2 p3 - pos c0 c1 c2 c3 - coin)
  (:init 
    (dec_f f1 f0) (dec_p p1 p0) (dec_p p2 p1) (dec_p p3 p2) (shaft e0 p0) 
    (shaft e1 p3)
(in e0 f0)
(in e1 f0) 
    (cpt (coin-at c0 f1 p0) 0.25) 
    (cpt  (coin-at c0 f1 p1) 0.25) 
    (cpt  (coin-at c0 f1 p2) 0.25)
    (cpt  (coin-at c0 f1 p3) 0.25)
    (multi (coin-at c0 f1 p0) (coin-at c0 f1 p1) (coin-at c0 f1 p2) (coin-at c0 f1 p3)) 
     (cpt (coin-at c1 f1 p0) 0.25) (cpt  (coin-at c1 f1 p1) 0.25) (cpt  (coin-at c1 f1 p2) 0.25) (cpt  (coin-at c1 f1 p3) 0.25)
    (multi (coin-at c1 f1 p0) (coin-at c1 f1 p1) (coin-at c1 f1 p2) (coin-at c1 f1 p3)) 
    (cpt (coin-at c2 f1 p0) 0.25) (cpt  (coin-at c2 f1 p1) 0.25) (cpt  (coin-at c2 f1 p2) 0.25) (cpt  (coin-at c2 f1 p3) 0.25)
    (multi (coin-at c2 f1 p0) (coin-at c2 f1 p1) (coin-at c2 f1 p2) (coin-at c2 f1 p3)) 
    (cpt (coin-at c3 f0 p0) 0.25) (cpt  (coin-at c3 f0 p1) 0.25) (cpt  (coin-at c3 f0 p2) 0.25) (cpt  (coin-at c3 f0 p3) 0.25)
    (multi (coin-at c3 f0 p0) (coin-at c3 f0 p1) (coin-at c3 f0 p2) (coin-at c3 f0 p3)) 
    (located f0 p0)
    
    
       
  )
  (:goal 0.9
  (and (have c0) (have c1) (have c2) (have c3)))
)
