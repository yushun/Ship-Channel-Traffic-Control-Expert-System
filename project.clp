(clear)
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
  ;(ship (number 5) (location Atlantic) (destination Gulf) (arrival-time 35)
  ;  (desired-time 300)(length 130)(width 40)(status ready))
  ;(ship (number 6) (location Gulf) (destination Atlantic) (arrival-time 40)
  ;  (desired-time 310)(length 120)(width 30)(status ready))
  ;(ship (number 7) (location Gulf) (destination Atlantic) (arrival-time 45)
  ;  (desired-time 320)(length 110)(width 40)(status ready))
  ;(ship (number 8) (location Gulf) (destination Atlantic) (arrival-time 50)
  ;  (desired-time 350)(length 60)(width 20)(status ready))
  ;(ship (number 9) (location Gulf) (destination Atlantic) (arrival-time 55)
  ;  (desired-time 350)(length 130)(width 45)(status ready))
  ;(ship (number 10) (location Atlantic) (destination Gulf) (arrival-time 55)
  ;  (desired-time 350)(length 135)(width 50)(status ready))
  ;(ship (number 11) (location Atlantic) (destination Gulf) (arrival-time 60)
  ;  (desired-time 380)(length 140)(width 50)(status ready))
  ;(ship (number 12) (location Atlantic) (destination Gulf) (arrival-time 70)
  ;  (desired-time 350)(length 195)(width 100)(status ready))
  ;(ship (number 13) (location Gulf) (destination Atlantic) (arrival-time 70)
  ;  (desired-time 350)(length 90)(width 30)(status ready))
  ;(ship (number 14) (location Gulf) (destination Atlantic) (arrival-time 80)
  ;  (desired-time 450)(length 105)(width 30)(status ready))
  ;(ship (number 15) (location Gulf) (destination Atlantic) (arrival-time 85)
  ;  (desired-time 480)(length 55)(width 20)(status ready))
  ;(ship (number 16) (location Atlantic) (destination Gulf) (arrival-time 85)
  ;  (desired-time 400)(length 60)(width 20)(status ready))
  ;(ship (number 17) (location Atlantic) (destination Gulf) (arrival-time 90)
  ;  (desired-time 410)(length 65)(width 15)(status ready))
  ;(ship (number 18) (location Gulf) (destination Atlantic) (arrival-time 90)
  ;  (desired-time 400)(length 65)(width 20)(status ready))
  ;(ship (number 19) (location Gulf) (destination Atlantic) (arrival-time 95)
  ;  (desired-time 345)(length 70)(width 30)(status ready))
  ;(ship (number 20) (location Atlantic) (destination Gulf) (arrival-time 100)
  ;  (desired-time 350)(length 85)(width 30)(status ready))
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


;;;;;;;;;;;;;;;;;;;;;;;;;
; traveling through locks
;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule situation-ship-channel-to-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) 
               (width ?ship-width) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection $? ?next-to-lock ?lock $? ?destination)
  (connection $? ?lock ?next-place $?)
  ?s3 <- (nonlock (name ?next-to-lock) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-lock"  "?time"  "?lock crlf)
  (printout t ?time"  "?num"  enters  "?lock"  "(+ ?time-needed ?time)"  "?next-place crlf)
  (printout t ?time"  "?lock"  changes  left  "(+ ?time-needed ?time)"  right" crlf)
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position left-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-channel-to-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) 
               (width ?ship-width) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  ?s3 <- (nonlock (name ?next-to-lock) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?lock ?next-to-lock $?)
  (connection $? ?next-place ?lock $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-lock"  "?time"  "?lock crlf)
  (printout t ?time"  "?num"  enters  "?lock"  "(+ ?time-needed ?time)"  "?next-place crlf)
  (printout t ?time"  "?lock"  changes  right  "(+ ?time-needed ?time)"  left" crlf)
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position right-close) (open-time ?sum) (ships ?num))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-lock-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships))
  (connection ?next-to-lock ?lock $? ?destination)
  (connection $? ?lock ?next-place $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time"  "?num"  arrives  "?next-to-lock"  "?time"  "?lock crlf)
  (printout t ?time"  "?num"  enters  "?lock"  "?sum"  "?next-place crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position left-close) (open-time ?sum) (ships ?num))
)

(defrule situation-ship-start-to-lock-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))
  (connection ?destination $? ?lock ?next-to-lock)
  (connection $? ?next-place ?lock $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (bind ?sum (+ ?time ?time-needed))
  (printout t ?time"  "?num"  arrives  "?next-to-lock"  "?time"  "?lock crlf)
  (printout t ?time"  "?num"  enters  "?lock"  "?sum"  "?next-place crlf)
  (modify ?s1 (location ?lock) (arrival-time ?sum) (status busy))
  (modify ?s2 (position right-close) (open-time ?sum) (ships ?num))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  cannot got into lock
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule situation-ship-activates-lock-change-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position right) (ships))  
  (connection $? ?next-to-lock ?lock $? ?destination)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (arrival-time ?sum) (status waiting))
  (modify ?s2 (position right-close) (open-time ?sum))
)

(defrule situation-ship-activates-lock-change-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) (status ready))
  ?s2 <- (lock (name ?lock) (time ?time-needed) (position left) (ships)) 
  (connection ?destination $? ?lock ?next-to-lock $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-lock) (destination ?destination)))
=>
  (printout t ?time"  "?lock"  arrives  right  "?time"  right" crlf)
  (bind ?sum (+ ?time ?time-needed))
  (modify ?s1 (arrival-time ?sum) (status waiting))
  (modify ?s2 (position left-close) (open-time ?sum))
)

(defrule situation-ship-cannot-go-into-lock-with-ship
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) 
               (arrival-time ?time) (status ready))
  (lock (name ?lock) (ships ?ship2) (open-time ?otime&:(> ?otime ?time)))
  (not (ship (number ?num2&:(< ?num2 ?num)) (arrival-time ?time)))
  (or
    (connection ?destination $? ?lock ?next-to-lock $?)
    (connection $? ?next-to-lock ?lock $? ?destination)
  )  
=>
  (modify ?s1 (arrival-time ?otime) (status waiting))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   waiting for locks change
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule situation-ship-cannot-go-into-lock-changing
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-lock) (destination ?destination) 
               (arrival-time ?time) (status ready))
  (not (ship (number ?num2&:(< ?num2 ?num)) (arrival-time ?time)))
  
  (or (lock (name ?lock) (open-time ?new-time&:(> ?new-time ?time)) (position left-close)  (ships))  ; the lock is changing 
      (lock (name ?lock) (open-time ?new-time&:(> ?new-time ?time)) (position right-close) (ships)))
  
  (or (connection ?destination $? ?lock ?next-to-lock $?)
      (connection $? ?next-to-lock ?lock $? ?destination))
=>
  (modify ?s1 (arrival-time ?new-time) (status waiting))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  open lock positions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule lock-open-right-side
  (current-time ?time)
  ?s2 <- (lock (name ?lock) (position left-close) (open-time ?time))
=>
  (printout t ?time"  "?lock"  arrives  right  "?time"  right" crlf)
  (modify ?s2 (position right))
)

(defrule lock-open-left-side
  (current-time ?time)
  ?s2 <- (lock (name ?lock) (position right-close) (open-time ?time))
=>
  (printout t ?time"  "?lock"  arrives  left  "?time"  left" crlf)
  (modify ?s2 (position left))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Traveling through channels
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule situation-ship-channel-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
               (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  ?s3 <- (nonlock (name ?next-to-waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection $? ?next-to-waterway ?name $? ?destination)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
               (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  ?s3 <- (lock (name ?next-to-waterway) (position right) (ships ?num))
  (connection $? ?next-to-waterway ?name $? ?destination)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-waterway"  "?time"  "?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (ships))
)

(defrule situation-ship-start-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
         (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  (connection ?next-to-waterway ?name $? ?destination)
  (connection $? ?name ?next-place $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-waterway"  "?time"  "?name crlf)
  (printout t ?time"  "?num"  enters  "?name"  "(+ ?time-needed ?time)"  "?next-place crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)

(defrule situation-ship-channel-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
         (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  ?s3 <- (nonlock (name ?next-to-waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?name ?next-to-waterway $?)
  (connection $? ?next-place ?name $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-waterway"  "?time"  "?name crlf)
  (printout t ?time"  "?num"  enters  "?name"  "(+ ?time-needed ?time)"  "?next-place crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (width =(+ ?waterway-width ?ship-width)) (ships $?list1 $?list2))
)

(defrule situation-ship-lock-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
         (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  ?s3 <- (lock (name ?next-to-waterway) (position left) (ships $?list1 ?num $?list2))
  (connection ?destination $? ?name ?next-to-waterway $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-waterway"  "?time"  "?name crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
  (modify ?s3 (ships $?list1 $?list2))
)

(defrule situation-ship-start-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination) 
         (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?name) (width ?width&:(> ?width ?ship-width)) (time ?time-needed) (ships $?ships))
  (connection ?destination $? ?name ?next-to-waterway)
  (connection $? ?next-place ?name $?)
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (printout t ?time"  "?num"  arrives  "?next-to-waterway"  "?time"  "?name crlf)
  (printout t ?time"  "?num"  enters  "?name"  "(+ ?time-needed ?time)"  "?next-place crlf)
  (modify ?s1 (location ?name) (arrival-time =(+ ?time ?time-needed)) (status busy))
  (modify ?s2 (width =(- ?width ?ship-width)) (ships ?num $?ships))
)


;;;;;;;;;;;;;;;;;;;;;;;;;
;  waiting 
;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;
;waiting channel to channel bc lower number ship comming into ur channel

(defrule situation-waiting-channel-to-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?channel) (width ?width)
               (destination ?destination) (arrival-time ?time) (status ready))
  (nonlock (name ?channel) (width ?channel-width))
  (connection $? ?channel ?next-channel $? ?destination)
  (nonlock (name ?next-channel) (width ?channel-width2&:(<= ?channel-width2 ?width)) (ships $? ?num2 $?))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?next-channel) (width ?width2&:(< ?width2 ?channel-width)) 
        (destination ~?destination) (arrival-time ?new-time))
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (modify ?s1 (arrival-time ?new-time) (status waiting))
)

(defrule situation-waiting-channel-to-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?channel) (width ?width)
               (destination ?destination) (arrival-time ?time) (status ready))
  (nonlock (name ?channel) (width ?channel-width))
  (connection ?destination $? ?next-channel ?channel $?)
  (nonlock (name ?next-channel) (width ?channel-width2&:(<= ?channel-width2 ?width)) (ships $? ?num2 $?))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?next-channel) (width ?width2&:(< ?width2 ?channel-width)) 
        (destination ~?destination) (arrival-time ?new-time))
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (modify ?s1 (arrival-time ?new-time) (status waiting))
)

;;;;;;;;;;;;;;;;;;;;;;
; channel to channel ship going the same dir

(defrule situation-waiting-channel-to-channel-same-dir
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?channel) (width ?width)
               (destination ?destination) (arrival-time ?time) (status ready))
  (nonlock (name ?channel))
  (or
    (connection $? ?channel ?next-channel $? ?destination)
    (connection ?destination $? ?next-channel ?channel $?)
  )
  (nonlock (name ?next-channel) (width ?channel-width&:(<= ?channel-width ?width)) (ships $? ?num2 $?))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?next-channel) 
        (destination ?destination) (arrival-time ?new-time))
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (modify ?s1 (arrival-time ?new-time) (status waiting))
)

(defrule situation-waiting-ship-channel-to-channel
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
               (arrival-time ?time) (width ?ship-width) (status ready))
         (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)
               (arrival-time ?new-time&:(> ?new-time ?time)))
=>
  (modify ?s1 (arrival-time ?new-time))
)

;;;;;;;;;;;;;;;;;;;;;;;;;
; waiting at start

(defrule situation-waiting-ship-at-start
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-waterway) (destination ?destination)
         (arrival-time ?time) (width ?ship-width) (status ready))
  (nonlock (name ?name) (width ?width&:(<= ?width ?ship-width)) (ships $? ?num2 $?))
  (connection ?next-to-waterway ?name $? ?destination)
  (not (ship (number ?num4&:(< ?num4 ?num)) (location ?next-to-waterway) (destination ?destination) (arrival-time ?time)))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?name) (arrival-time ?new-time&:(> ?new-time ?time)))
  (not(ship(number ?num3&:(< ?num3 ?num)) (location ?name) (arrival-time ?x&:(< ?x ?new-time))))
=>
  (modify ?s1 (arrival-time ?new-time) (status waiting))
)

;;;;;;;;;;;;;;;;;;;;;;;;;
; Reverse
;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule reverse-ship-lock-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?lock) (width ?width)
               (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (position right) (time ?lock-time))
  (connection $? ?lock ?channel $? ?destination)
  (nonlock (name ?channel) (width ?channel-width&:(<= ?channel-width ?width)) (ships $? ?num2 $?))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?channel) (destination ~?destination))
=>
  (bind ?sum (+ ?time ?lock-time))
  (modify ?s1 (arrival-time ?sum) (status reverse))
  (modify ?s2 (open-time ?sum) (position right-close))
  (assert (reverse ?num ?num2))
  
)

(defrule reverse-ship-lock-channel-westward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?lock) (width ?width)
               (destination ?destination) (arrival-time ?time) (status ready))
  ?s2 <- (lock (name ?lock) (position left) (time ?lock-time))
  (connection ?destination $? ?channel ?lock $? )
  (nonlock (name ?channel) (width ?channel-width&:(<= ?channel-width ?width)) (ships $? ?num2 $?))
  (ship (number ?num2&:(< ?num2 ?num)) (location ?channel) (destination ~?destination))
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (bind ?sum (+ ?time ?lock-time))
  (modify ?s1 (arrival-time ?sum) (status reverse))
  (modify ?s2 (open-time ?sum) (position left-close))
  (assert (reverse ?num ?num2))
)

(defrule reverse-out-of-lock-channel-eastward
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?lock) (width ?width) (arrival-time ?time)
               (destination ?destination) (status reverse))
  ?s2 <- (lock (name ?lock) (position left) (ships ?num))
  (connection $? ?channel ?lock $? ?destination)
  ?s3 <- (nonlock (name ?channel) (width ?channel-width&:(> ?channel-width ?width)) (ships $?ships))
  (reverse ?num ?num2)
  (ship (number ?num2) (arrival-time ?new-time))
=>
  (modify ?s1 (location ?channel) (arrival-time ?new-time) (status reverse-wait))
  (modify ?s2 (ships))
  (modify ?s3 (width =(- ?channel-width ?width)) (ships ?num $?ships))
)

(defrule ship-reverse-waiting-update
  (current-time ?time)
  ?s1 <- (ship (number ?num) (arrival-time ?time) (location ?location) (status reverse-wait))
  (reverse ?num ?num2)
  (ship (number ?num2) (arrival-time ?new-time&:(> ?new-time ?time)) (location ~?location))
=>
  (modify ?s1 (arrival-time ?new-time))
)

(defrule ship-reverse-waiting-ready
  (current-time ?time)
  ?s1 <- (ship (number ?num) (arrival-time ?time) (location ?location) (status reverse-wait))
  ?s2 <- (reverse ?num ?num2)
  (ship (number ?num2) (location ?location))
=>
  (modify ?s1 (status ready))
  (retract ?s2)
)

;;;;;;;;;;;;;;;;;;;;;;;;;
; to goal
;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule situation-ship-channel-to-goal
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?next-to-goal) (destination ?destination) 
  (arrival-time ?time) (width ?ship-width) (status ready))
  ?s2 <- (nonlock (name ?next-to-goal) (width ?channel-width) (ships $?list1 ?num $?list2))
  (or
    (connection $? ?next-to-goal ?destination)
    (connection ?destination ?next-to-goal $?)
  )
  (not (ship (number ?num2&:(< ?num2 ?num)) (location ?next-to-waterway) (destination ?destination)))
=>
  (retract ?s1) (assert (finish ?num ?time))
  (modify ?s2 (width =(+ ?channel-width ?ship-width)) (ships $?list1 $?list2))
)


;;;;;;;;;;;;;;;;;;;;;;;;;
; end
;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule move-ship-out-of-waterway
  ?s3 <- (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?waterway) (arrival-time ?time) (status ?status))
  (or (test(eq ?status waiting)) (test(eq ?status busy)))
  ?s2 <- (nonlock (name ?waterway) (width ?waterway-width) (ships $?list1 ?num $?list2))
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (modify ?s1 (status ready))
)

(defrule move-ship-out-of-lock
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?lock) (arrival-time ?time) (status ?status))
  (or (test(eq ?status waiting)) (test(eq ?status busy)))
  ?s2 <- (lock (name ?lock) (ships ?num) (position ?pos) (open-time ?time))
=>
  (modify ?s1 (status ready))
)

(defrule move-ship-out-of-start
  (current-time ?time)
  ?s1 <- (ship (number ?num) (location ?start) (arrival-time ?time) (status waiting))
  (or
    (connection ?start $? ?destination)
    (connection ?destination $? ?start)
  )
  (not (ship (number ?num3&:(< ?num3 ?num)) (arrival-time ?time)))
=>
  (modify ?s1 (status ready))
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

