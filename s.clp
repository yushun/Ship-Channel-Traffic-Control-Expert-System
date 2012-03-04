
(deftemplate ship
  (slot number)
  (slot location)
  (slot destination)
  (slot arrival-time)
  (slot desired-time)
  (slot length)
  (slot width)
  (slot status)        ;ready, busy, finished
)

(deftemplate nonlock
  (slot name)
  (slot width)
  (slot time)
  (multislot ships)
)

(deftemplate lock
  (slot name)
  (slot time)
  (slot length)
  (slot position)
  (slot open-time)
  (multislot ships)        ;should only have one ship
)

(deffacts ships
  (ship (number 1) (location Gulf) (destination Atlantic) (arrival-time 0)
    (desired-time 300)(length 100)(width 50)(status ready))
)

(deffacts locks
  (lock (name InglisLock)  (time 10) (length 300) (position left) (open-time 0))
  (lock (name DoshLock)    (time 20) (length 200) (position left) (open-time 0))
  (lock (name BuckmanLock) (time 20) (length 300) (position left) (open-time 0))
)

(deffacts nonlocks
  (nonlock (name InglisChannel) (width 230)  (time 40))
  (nonlock (name LakeDosh)      (width 1000) (time 40))
  (nonlock (name DoshChannel)   (width 150)  (time 30))
  (nonlock (name LakeOcklawaha) (width 1500) (time 40))
  (nonlock (name StJohnsRiver)  (width 1000) (time 50)) 
)

(deffacts map
  (connection Gulf InglisChannel InglisLock LakeDosh DoshLock DoshChannel LakeOcklawaha BuckmanLock StJohnsRiver Atlantic)
)

(deffacts startTime
  (current-time 0)
)

(defrule situation-ship-go-into-lock-eastward
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection $? ?next-to-lock ?lock $? ?destination)
  (current-time ?time)
=>
  (modify ?s1 (location ?lock) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (position left-close) (open-time =(+ ?time ?time-needed)) (ships ?num))
)

(defrule lock-open-right-side
  (current-time ?time)
  ?s2 <- (lock (position left-close) (open-time ?otime))
  (test (eq ?time ?otime))
=>
  (modify ?s2 (position right))
)

(defrule lock-open-left-side
  (current-time ?time)
  ?s2 <- (lock (position right-close) (open-time ?otime))
  (test (eq ?time ?otime))
=>
  (modify ?s2 (position left))
)

(defrule situation-ship-go-into-channel-eastward
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  (connection $? ?next-to-waterway ?name $? ?destination)
  (current-time ?time)
=>
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)

;; this replaces clear-ship-from-waterwaylist
(defrule move-ship-out-of-waterway
  ?s1 <- (ship (number ?num) (width ?ship-width) (location ?location) (arrival-time ?atime))
  ?s2 <- (nonlock (name ?waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (current-time ?time)
  (test (eq ?location ?waterway))
  (test (eq ?time ?atime))
=>
  (modify ?s1 (status ready))
  (modify ?s2 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule move-ship-out-of-lock
  ?s1 <- (ship (number ?num) (location ?location))
  ?s2 <- (lock (name ?waterway) (ships ?num) (open-time ?otime))
  (current-time ?time)
  (test (eq ?location ?waterway))
  (test (eq ?time ?otime))
=>
  (modify ?s1 (status ready))
  (modify ?s2 (ships))
)

;(defrule clear-ship-from-waterwaylist
;  ?s1 <- (nonlock (name ?waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
;  ?s2 <- (ship (number ?num) (width ?ship-width) (location ?location))
;  (test (neq ?location ?waterway))
;=>
;  (modify ?s1 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
;)

;(defrule clear-ship-from-lock
;  ?s1 <- (lock (name ?waterway) (ships ?num))
;  ?s2 <- (ship (number ?num) (location ?location))
;  (test (neq ?location ?waterway))
;=>
;  (modify ?s1 (ships))
;)

(defrule situation-ship-to-goal
  ?s1 <- (ship (number ?num) (location ?next-to-goal) (destination ?destination) 
  (arrival-time ?time) (width ?ship-width) (status ready))
  (or
    (connection $? ?next-to-goal ?destination)
    (connection ?destination ?next-to-goal $?)
  )
  (current-time ?time)
=>
  (modify ?s1 (location ?destination) (status finish))
)

(defrule update-time
  ?cur-time <- (current-time ?time)
  (ship (arrival-time ?new-time&:(neq ?time ?new-time)))
  (not (ship(arrival-time ?x&:(< ?x ?new-time))))
=>
  (retract ?cur-time)
  (assert (current-time ?new-time))
)

