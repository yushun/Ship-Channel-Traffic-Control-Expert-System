(clear)
(deftemplate ship
  (slot number)
  (slot location)
  (slot destination)
  (slot arrival-time)
  (slot desired-time)
  (slot length)
  (slot width)
  (slot status)        ;ready,waiting, busy, finished
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
  (ship (number 2) (location Gulf) (destination Atlantic) (arrival-time 10)
    (desired-time 300)(length 100)(width 75)(status ready))
  (ship (number 3) (location Atlantic) (destination Gulf) (arrival-time 20)
    (desired-time 350)(length 80)(width 75)(status ready))
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

;;
; traveling through locks

(defrule situation-ship-go-into-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection $? ?next-to-lock ?lock $? ?destination)
=>
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position left-close) (open-time ?sum) (ships ?num))
)

(defrule situation-ship-cannot-go-into-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))  ; the lock is on the other way and there are no ships
  (connection $? ?next-to-lock ?lock $? ?destination)
=>
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (arrival-time ?sum))
  (modify ?s2 (position right-close) (open-time ?sum))
)


(defrule situation-ship-go-into-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  (connection ?destination $? ?lock ?next-to-lock $?)
=>
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position right-close) (open-time ?sum) (ships ?num))
)

(defrule situation-ship-cannot-go-into-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))  ; the lock is on the other way and there are no ships
  (connection ?destination $? ?lock ?next-to-lock $?)
=>
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (arrival-time ?sum))
  (modify ?s2 (position left-close) (open-time ?sum))
)

(defrule lock-open-right-side
  (current-time ?time)
  ?s2 <- (lock (position left-close) (open-time ?time))
=>
  (modify ?s2 (position right))
)

(defrule lock-open-left-side
  (current-time ?time)
  ?s2 <- (lock (position right-close) (open-time ?time))
=>
  (modify ?s2 (position left))
)

;;
; Traveling through channels

(defrule situation-ship-go-into-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  (connection $? ?next-to-waterway ?name $? ?destination)
=>
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)

(defrule situation-ship-go-into-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  (connection ?destination $? ?name ?next-to-waterway $?)
=>
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)

(defrule situation-ship-cannot-into-channel-eastward-not-enough-width
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (<= ?width ?ship-width))
  (connection $? ?next-to-waterway ?name $? ?destination)
  (ship (number ~?num) (arrival-time ?new-time&:(> ?new-time ?time)) )
  (not (ship (number ~?num) (arrival-time ?x&:(< ?x ?new-time))))
=>
  (modify ?s1 (arrival-time ?new-time))
)

(defrule situation-ship-cannot-into-channel-westward-not-enough-width
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (<= ?width ?ship-width))
  (connection ?destination $? ?name ?next-to-waterway $?)
  (ship (number ~?num) (arrival-time ?new-time&:(> ?new-time ?time)) )
  (not (ship (number ~?num) (arrival-time ?x&:(< ?x ?new-time))))
=>
  (modify ?s1 (arrival-time ?new-time))
)

(defrule move-ship-out-of-waterway
  ?s3 <- (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?waterway) (destination ?d) (length ?l) (width ?ship-width) (arrival-time ?time))
  ?s2 <- (nonlock (name ?waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
=>
  (modify ?s1 (status ready))
  (modify ?s2 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule move-ship-out-of-lock
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?waterway))
  ?s2 <- (lock (name ?waterway) (ships ?num) (open-time ?time))
=>
  (modify ?s1 (status ready))
  (modify ?s2 (ships))
)

(defrule situation-ship-to-goal
  ?s1 <- (ship (number ?num) (location ?next-to-goal) (destination ?destination) 
  (arrival-time ?time) (width ?ship-width) (status ready))
  (or
    (connection $? ?next-to-goal ?destination)
    (connection ?destination ?next-to-goal $?)
  )
  (current-time ?time)
=>
  ;(modify ?s1 (location ?destination) (status finish))
  (retract ?s1) (assert (finish ?num))
)

(defrule update-time
  ?cur-time <- (current-time ?time)
  (ship (arrival-time ?new-time&:(neq ?time ?new-time)))
  (not (ship(arrival-time ?x&:(< ?x ?new-time))))
=>
  (retract ?cur-time)
  (assert (current-time ?new-time))
)

(reset)
(run)
