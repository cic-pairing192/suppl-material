/*
 * RELIC is an Efficient LIbrary for Cryptography
 * Copyright (c) 2009 RELIC Authors
 *
 * This file is part of RELIC. RELIC is legal property of its developers,
 * whose names are not listed here. Please refer to the COPYRIGHT file
 * for contact information.
 *
 * RELIC is free software; you can redistribute it and/or modify it under the
 * terms of the version 2.1 (or later) of the GNU Lesser General Public License
 * as published by the Free Software Foundation; or version 2.0 of the Apache
 * License as published by the Apache Software Foundation. See the LICENSE files
 * for more details.
 *
 * RELIC is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the LICENSE files for more details.
 *
 * You should have received a copy of the GNU Lesser General Public or the
 * Apache License along with RELIC. If not, see <https://www.gnu.org/licenses/>
 * or <https://www.apache.org/licenses/>.
 */

/**
 * @file
 *
 * Implementation of the basic functions to temporary double precision digit
 * vectors.
 *
 * @ingroup dv
 */

#include <inttypes.h>

#include "relic_core.h"

/*============================================================================*/
/* Public definitions                                                         */
/*============================================================================*/

void dv_print(const dig_t *a, size_t digits) {
	/* Suppress possible unused parameter warning. */
	(void)a;
	for (size_t i = digits; i > 0; i--) {
		util_print_dig(a[i-1], 1);
	}
	util_print("\n");

	return;
}

void dv_zero(dig_t *a, size_t digits) {
	int i;

#if ALLOC != DYNAMIC
	if (digits > RLC_DV_DIGS) {
		RLC_THROW(ERR_NO_PRECI);
		return;
	}
#endif

	for (i = 0; i < digits; i++, a++) {
		(*a) = 0;
	}

	return;
}

void dv_copy(dig_t *c, const dig_t *a, size_t digits) {
	memcpy(c, a, digits * sizeof(dig_t));
}

void dv_copy_sec(dig_t *c, const dig_t *a, size_t digits, dig_t bit) {
	dig_t mask, t;

	mask = -bit;
	for (size_t i = 0; i < digits; i++) {
		t = (a[i] ^ c[i]) & mask;
		c[i] ^= t;
	}
}

void dv_swap_sec(dig_t *c, dig_t *a, size_t digits, dig_t bit) {
	dig_t mask, t;

	mask = -bit;
	for (size_t i = 0; i < digits; i++) {
		t = (a[i] ^ c[i]) & mask;
		a[i] ^= t;
		c[i] ^= t;
	}
}

int dv_cmp(const dig_t *a, const dig_t *b, size_t size) {
	int r;

	a += (size - 1);
	b += (size - 1);

	r = RLC_EQ;
	for (size_t i = 0; i < size; i++, --a, --b) {
		if (*a != *b && r == RLC_EQ) {
			r = (*a > *b ? RLC_GT : RLC_LT);
		}
	}
	return r;
}

int dv_cmp_sec(const dig_t *a, const dig_t *b, size_t size) {
	dig_t r = 0;

	for (size_t i = 0; i < size; i++) {
		r |= a[i] ^ b[i];
	}

	return (r == 0 ? RLC_EQ : RLC_NE);
}

void dv_rshd(dig_t *c, const dig_t *a, size_t size, uint_t digits) {
	const dig_t *top;
	dig_t *bot;
	size_t i;

	top = a + digits;
	bot = c;

	for (i = 0; i < size - digits; i++, top++, bot++) {
		*bot = *top;
	}
	for (; i < size; i++, bot++) {
		*bot = 0;
	}
}

void dv_lshd(dig_t *c, const dig_t *a, size_t size, uint_t digits) {
	dig_t *top;
	const dig_t *bot;
	size_t i;

	top = c + size - 1;
	bot = a + size - 1 - digits;

	for (i = 0; i < size - digits; i++, top--, bot--) {
		*top = *bot;
	}
	for (i = 0; i < digits; i++, c++) {
		*c = 0;
	}
}
