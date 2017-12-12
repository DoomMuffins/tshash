import collections
from bitstring import BitArray, Bits
from sage.all import GF

_BITS = (Bits('0b0'), Bits('0b1'))
_SKIP_PRIMITIVITY_CHECK = False
_MITM_DEFAULT_MAX_LENGTH = 32
_POLY_RING = GF(2)['x']


def bits_to_polynomial(bits):

    result = _POLY_RING.zero()
    for i, bit in enumerate(reversed(bits)):
        result += bit * (_POLY_RING.gen() ** i)
    return result


def polynomial_to_bits(poly):
    field = poly.base_ring()
    radix = field.characteristic()
    assert radix == 2, 'Weird radix'

    coefficients = poly.coefficients(sparse=False)
    return Bits(map(int, reversed(coefficients)))


def bits_to_polynomial_modulo(bits):
    return _POLY_RING.gen()**bits.len + bits_to_polynomial(bits)


def polynomial_modulo_to_bits(poly):
    return polynomial_to_bits(poly - _POLY_RING.gen()**poly.degree())


def extend_bits_to_width(bits, width):
    assert bits.len <= width, 'Already wide enough'
    return Bits(width - bits.len) + bits


class TSHashParams(object):
    def __init__(self, width, initial_value, polynomials):
        self.width = width
        self.initial_value = self._canonize_initial_value(extend_bits_to_width(initial_value, self.width))

        assert len(polynomials) == 2, 'Weird amount of polynomials'

        if not _SKIP_PRIMITIVITY_CHECK:
            for poly in polynomials:
                poly_object = bits_to_polynomial(poly)
                poly_ring = poly_object.parent()

                actual_poly_object = poly_ring.gen() ** self.width + poly_object
                assert actual_poly_object.is_primitive(), 'The feedback polynomials must be primitive'

        self.polynomials = tuple(extend_bits_to_width(poly, self.width) for poly in polynomials)

    def __repr__(self):
        return '{typename}(width={width}, initial_value={initial_value}, polynomials={polynomials})'.format(
            typename=type(self).__name__,
            width=self.width,
            initial_value=bits_to_polynomial(self.initial_value),
            polynomials=tuple(bits_to_polynomial_modulo(p) for p in self.polynomials)
        )

    @classmethod
    def _canonize_initial_value(cls, uncanonized_initial_value):
        last_one_bit_position = uncanonized_initial_value.rfind(_BITS[1])
        assert last_one_bit_position, 'Initial value supplied is zero'
        shift_amount = uncanonized_initial_value.len - last_one_bit_position[0] - 1
        return uncanonized_initial_value >> shift_amount


class TSHash(object):
    def __init__(self, tshash_params):
        self._params = tshash_params
        self._state = self._params.initial_value

    def update(self, data):
        for d in data:
            self._state = self.calculate_new_state(self._params, self._state, d)

    def digest(self):
        return self._state

    def reset(self):
        self._state = self._params.initial_value

    def compute(self, data):
        self.reset()
        self.update(data)
        return self.digest()

    @classmethod
    def calculate_new_state(cls, tshash_params, current_state, bit):
        current_polynomial = tshash_params.polynomials[bit]
        shift_amount = 1 + current_state.find(_BITS[1])[0]
        new_state = (current_state << shift_amount) ^ current_polynomial
        return new_state


def mitm(tshash_params, state_to_postfix, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    # Starting conditions
    state_to_prefix = {tshash_params.initial_value: Bits()}
    advance_forward = True
    current_length = 0

    while current_length <= max_length:
        # Check whether we have a collision
        for state, postfix in state_to_postfix.iteritems():
            prefix = state_to_prefix.get(state)
            if prefix is not None:
                preimage = prefix + postfix
                if preimage not in except_bitstrings:
                    return preimage

        if advance_forward:
            # Advance the prefixes
            new_state_to_prefix = {}
            for state, prefix in state_to_prefix.iteritems():
                for bit in _BITS:
                    new_state = TSHash.calculate_new_state(tshash_params, state, bit[0])
                    new_prefix = prefix + bit
                    new_state_to_prefix[new_state] = new_prefix
            state_to_prefix = new_state_to_prefix

        else:
            # Advance the postfixes
            new_state_to_postfix = {}
            for state, postfix in state_to_postfix.iteritems():
                for bit in _BITS:
                    new_postfix = bit + postfix
                    polynomial = tshash_params.polynomials[bit[0]]

                    # Revert last generator multiplication
                    new_state = BitArray(bin=state.bin)  # Workaround for aliasing bug
                    new_state ^= polynomial
                    new_state >>= 1
                    new_state[0] = True
                    new_state >>= new_state.len - new_state.rfind(_BITS[1])[0] - 1
                    new_state = Bits(new_state)

                    assert TSHash.calculate_new_state(tshash_params, new_state, bit[0]) == state

                    new_state_to_postfix[new_state] = new_postfix

            state_to_postfix = new_state_to_postfix

        # Alternate between forward and backward
        advance_forward = not advance_forward
        current_length += 1

    return None


def mitm_state_preimage(tshash_params, state, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    state_to_postfix = {state: Bits()}
    return mitm(tshash_params, state_to_postfix, except_bitstrings)


def mitm_digest_preimage(tshash_params, digest, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    #possible_truncations = ('0b01', '0b11')
    possible_truncations = ('',)
    state_to_postfix = {digest + possible_truncation: Bits() for possible_truncation in possible_truncations}
    return mitm(tshash_params, state_to_postfix, except_bitstrings)


def mitm_second_preimage(tshash_params, bitstring, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    tshash = TSHash(tshash_params)
    digest = tshash.compute(bitstring)
    return mitm_digest_preimage(tshash_params, digest, except_bitstrings=(bitstring,) + except_bitstrings)


def get_state_to_preimages(tshash_params, depth=None):
    depth = depth or tshash_params.width
    state_to_preimages = collections.defaultdict(list)
    bfs = collections.deque()
    bfs.append((tshash_params.initial_value, Bits()))
    current_len = -1

    while bfs:
        state, preimage = bfs.popleft()
        state_to_preimages[state].append(preimage)

        if preimage.len > current_len:
            current_len = preimage.len
            print current_len

        if preimage.len < depth:
            for bit in _BITS:
                new_state = TSHash.calculate_new_state(tshash_params, state, bit[0])
                new_preimage = preimage + bit
                bfs.append((new_state, new_preimage))

    return state_to_preimages


def calculate_trajectory(tshash_params, bitstring):
    tshash = TSHash(tshash_params)
    trajectory = [tshash._state]
    for bit in bitstring:
        tshash.update([bit])
        trajectory.append(tshash._state)
    return trajectory

