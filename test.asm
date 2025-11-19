.org 0x80000000
.global _start

_start:
lui     t1, 0x000F4
addi    t1, t1, 0x240
li      t0, 0

loop_start:
addi    t0, t0, 1
xor     t2, t0, t1
add     t3, t0, t2
blt     t0, t1, loop_start

j       _start

.end
