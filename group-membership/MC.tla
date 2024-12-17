---- MODULE MC ----
EXTENDS groupmembership, TLC

CONSTANTS Alice, Bob

StateConstraint == \A <<x, y>> \in DevicePairs : Len(Queues[x, y]) <= MaxQueue

ClockConstraint == \A d \in AllDevices : clock[d] < MaxClock
=============================================================================
