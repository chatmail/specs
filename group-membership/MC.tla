---- MODULE MC ----
EXTENDS groupmembership, TLC

StateConstraint == \A <<x, y>> \in DevicePairs : Len(queues[x, y]) <= MaxQueue

ClockConstraint == clock < MaxClock
=============================================================================
