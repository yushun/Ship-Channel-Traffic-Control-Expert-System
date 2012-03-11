(clear)
;(watch facts)
;(watch rules)
(deftemplate ship
  (slot number)
  (slot location)
  (slot destination)
  (slot arrival-time)
  (slot desired-time)
  (slot length)
  (slot width)
  (slot status)        ;ready, waiting, busy, reverse, finished
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
    (desired-time 300)(length 75)(width 40)(status ready))
  (ship (number 3) (location Atlantic) (destination Gulf) (arrival-time 20)
    (desired-time 300)(length 200)(width 120)(status ready))
  (ship (number 4) (location Gulf) (destination Atlantic) (arrival-time 30)
    (desired-time 350)(length 80)(width 30)(status ready))
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

(defrule situation-ship-channel-to-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (width ?ship-width) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection $? ?next-to-lock ?lock $? ?destination)
  ?s3 <- (nonlock (name ?next-to-lock) (width ?waterway-width) (ships $?list1 ?num $?list2))
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  left  " (+ ?time ?time-needed) "  right" crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position left-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection $? ?next-to-lock ?lock $? ?destination)
  ?s3 <- (lock (name ?next-to-lock) (position right) (ships $?list1 ?num $?list2))
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  left  " (+ ?time ?time-needed) "  right" crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position left-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection ?next-to-lock ?lock $? ?destination)
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  left  " (+ ?time ?time-needed) "  right" crlf)
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
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  right  " (+ ?time ?time-needed) "  left" crlf)
  (modify ?s1 (arrival-time ?sum))
  (modify ?s2 (position right-close) (open-time ?sum))
)


(defrule situation-ship-channel-to-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (width ?ship-width) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  ?s3 <- (nonlock (name ?next-to-lock) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?lock ?next-to-lock $?)
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position right-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  (connection ?destination $? ?lock ?next-to-lock $?)
  ?s3 <- (lock (name ?next-to-lock) (position left) (ships $?list1 ?num $?list2))
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  right  " ?sum "  left" crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position right-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  (connection ?destination $? ?lock ?next-to-lock)
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time "  " ?num "  arrives  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?num "  enters  " ?lock "  " ?sum "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  right  " ?sum "  left" crlf)
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
  (printout t ?time "  " ?num "  enters  " ?next-to-lock "  " ?time "  " ?lock crlf)
  (printout t ?time "  " ?lock "  changes  left  " ?sum "  right" crlf)
  (modify ?s1 (arrival-time ?sum))
  (modify ?s2 (position left-close) (open-time ?sum))
)

(defrule situation-ship-cannot-go-into-lock-with-ship
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?ship1-time) (status ready))
  ?s2 <- (lock (name ?lock) (ships ?ship2))  ; the lock is on the other way and there are no ships
  ?s3 <- (ship (number ?ship2) (arrival-time ?ship2-time))
  (or
    (connection ?destination $? ?lock ?next-to-lock $?)
    (connection $? ?next-to-lock ?lock $? ?destination)
  )
  (test (neq ?ship1-time ?ship2-time))
=>
  (modify ?s1 (arrival-time ?ship2-time))
)

(defrule lock-open-right-side
  (current-time ?time)
  ?s2 <- (lock (name ?lock) (position left-close) (open-time ?time))
=>
  (modify ?s2 (position right))
  (printout t ?time "  " ?lock "  arrives  right  " ?time "  right" crlf)
)

(defrule lock-open-left-side
  (current-time ?time)
  ?s2 <- (lock (name ?lock) (position right-close) (open-time ?time))
=>
  (printout t ?time "  " ?lock "  arrives  left  " ?time "  left" crlf)
  (modify ?s2 (position left))
)

;;
; Traveling through channels

(defrule situation-ship-channel-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  ?s3 <- (nonlock (name ?next-to-waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection $? ?next-to-waterway ?name $? ?destination)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  ?s3 <- (lock (name ?next-to-waterway) (position right) (ships $?list1 ?num $?list2))
  (connection $? ?next-to-waterway ?name $? ?destination)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  (connection ?next-to-waterway ?name $? ?destination)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)

(defrule situation-ship-channel-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  ?s3 <- (nonlock (name ?next-to-waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?name ?next-to-waterway $?)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  ?s3 <- (lock (name ?next-to-waterway) (position left) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?name ?next-to-waterway $?)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (> ?width ?ship-width))
  (connection ?destination $? ?name ?next-to-waterway)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-waterway "  " ?time "  " ?name crlf)
  (printout t ?time "  " ?num "  enters  " ?name "  " (+ ?time ?time-needed) "  " ?name crlf)
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
  (ship (number ~?num) (arrival-time ?new-time&:(neq ?new-time ?time)) )
  (not (ship (number ~?num) (arrival-time ?x&:(< ?x ?new-time))))
=>
  (printout t ?time "  " ?num "  cannot go in  " ?name "  change time to  " ?new-time crlf)
  (modify ?s1 (arrival-time ?new-time))
)

(defrule situation-ship-cannot-into-channel-westward-not-enough-width
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
    (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width) (time ?time-needed) (ships $?ships))
  (test (<= ?width ?ship-width))
  (connection ?destination $? ?name ?next-to-waterway $?)
  (ship (number ~?num) (arrival-time ?new-time&:(neq ?new-time ?time)) )
  (not (ship (number ~?num) (arrival-time ?x&:(< ?x ?new-time))))
=>
  (printout t ?time "  " ?num "  cannot go in" ?name "  change time to  " ?new-time crlf)
  (modify ?s1 (arrival-time ?new-time))
)

(defrule move-ship-out-of-waterway
  ?s3 <- (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?waterway) (arrival-time ?time) (status busy))
  ?s2 <- (nonlock (name ?waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
=>
  (modify ?s1 (status ready))
)

(defrule move-ship-out-of-lock
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?lock) (status busy))
  ?s2 <- (lock (name ?lock) (ships ?num) (position ?pos) (open-time ?time))
=>
  (modify ?s1 (status ready))
)

(defrule situation-ship-channel-to-goal
  ?s1 <- (ship (number ?num) (location ?next-to-goal) (destination ?destination) 
  (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?next-to-goal) (width ?channel-width) (ships $?list1 ?num $?list2))
  (or
    (connection $? ?next-to-goal ?destination)
    (connection ?destination ?next-to-goal $?)
  )
  (current-time ?time)
=>
  ;(modify ?s1 (location ?destination) (status finish))
  (printout t ?time "  " ?num "  arrives  " ?next-to-goal "  " ?time "  " ?destination crlf)
  (retract ?s1) (assert (finish ?num))
  (modify ?s2 (width =(+ ?channel-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-goal
  ?s1 <- (ship (number ?num) (location ?next-to-goal) (destination ?destination) 
  (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (lock (name ?next-to-goal) (ships $?list1 ?num $?list2))
  (or
    (connection $? ?next-to-goal ?destination)
    (connection ?destination ?next-to-goal $?)
  )
  (current-time ?time)
=>
  (printout t ?time "  " ?num "  arrives  " ?next-to-goal "  " ?time "  " ?destination crlf)
  ;(modify ?s1 (location ?destination) (status finish))
  (retract ?s1) (assert (finish ?num))
  (modify ?s2 (ships $?list1 $?list2))
)

;;
; Ship reversing

(defrule situation-ship-reverse
  ;(declare-salience -10)
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?channel) (destination ?destination1)
           (arrival-time ?time) (length ?length1) (width ?width) (status ready))
  (ship (number ?num2) (location ?next-to-channel) 
     (length ?length2) (width ?width2) (status ready))
  (not (ship (location ?next-to-channel) (width ?x&:(< ?x ?width2)) (status ready)))
  (or
    (connection ?destination $? ?next-to-channel ?channel $?)
    (connection $? ?channel ?next-to-channel $? ?destination)
  )
  (nonlock (name ?channel) (width ?channel-width) (time ?time-needed) (ships $?ships))
  (test (< ?width2 (+ ?width ?channel-width)))
=> 
  (modify ?s1 (arrival-time (+ ?time ?time-needed)) (status reverse))
)

(defrule situation-ship-reversing-into-prev-channel
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?channel) (destination ?destination1)
           (arrival-time ?time) (length ?length1) (width ?width) (status reverse))
  (connection ?destination $? ?channel ?prev $?)
  ?s2 <- (nonlock (name ?channel) (width ?channel-width) (time ?time-needed) (ships $?ships1 ?num $?ships2))
  ?s3 <- (nonlock (name ?prev) (width ?prev-width&:(> ?prev-width ?width)) (ships $?ships2))
  
=> 
  (modify ?s1 (location ?prev) (arrival-time (+ ?time 1)) (status busy))
  (modify ?s2 (width (+ ?channel-width ?width)) (ships $?ships1 $?ships2))
  (modify ?s3 (width (- ?prev-width ?width)) (ships ?num $?ships2))
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
