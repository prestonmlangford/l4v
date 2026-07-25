/*
 * PolarFire verified multicore (AMP) -- Phase 4 (C half): minimal C
 * implementation of the channel status-word transition, mirrored against
 * Phase 4 R half's xchan_send_R / xchan_recv_ack_R (AMP_Channel_R.thy).
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *
 * Scope: only the status word is modelled here, exactly as buffer CONTENTS
 * remain unmodelled at every earlier phase. The memory fence a real
 * cross-core implementation needs around this store (see the "Mechanics
 * note -- IPI routing and the waiter table" in ../../multicore-amp-plan.md,
 * and assumption A-BIN) is a Phase 6 concern: this C is the sequential
 * store a fence would guard, not the fence itself.
 */

void xchan_send_c(unsigned *status)
{
    *status = 1;
}

void xchan_recv_ack_c(unsigned *status)
{
    *status = 0;
}
