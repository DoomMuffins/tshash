"""
This package provides a research-oriented pure Python implementation of TS-hash,
including utility functions and algorithms to examine the properties of particular
instantiations of TS-hash.

Classes:

TSHashParams -- The parameters (keys) of a particular function from the TS-hash family.
TSHash -- A stateful object providing a stream-based hash interface.
"""

import collections
from bitstring import BitArray, Bits
from sage.all import GF

_BITS = (Bits('0b0'), Bits('0b1'))
_SKIP_PRIMITIVITY_CHECK = False
_MITM_DEFAULT_MAX_LENGTH = 32
_POLY_RING = GF(2)['x']


def bits_to_polynomial(bits):
    """
    Converts a bitstring to a polynomial over GF(2) (MSB/highest exponent first).
    :param bits: The bitstring to convert.
    :return: The polynomial over GF(2) corresponding to the bitstring.
    """
    result = _POLY_RING.zero()
    for i, bit in enumerate(reversed(bits)):
        result += bit * (_POLY_RING.gen() ** i)
    return result


def polynomial_to_bits(poly):
    """
    Converts a polynomial over GF(2) to a bitstring (MSB/highest exponent first).
    :param poly: The polynomial to convert.
    :return: The bitstring corresponding to the polynomial over GF(2).
    """
    field = poly.base_ring()
    radix = field.characteristic()
    assert radix == 2, 'Weird radix'

    coefficients = poly.coefficients(sparse=False)
    return Bits(map(int, reversed(coefficients)))


def extend_bits_to_width(bits, width):
    assert bits.len <= width, 'Already wide enough'
    return Bits(width - bits.len) + bits


def bits_to_polynomial_modulo(bits):
    """
    Converts a bitstring to a TS-hash polynomial modulo, including the unrepresented
    x^n term (MSB/highest exponent first). Assumes the bitstring's length is equal
    to the polynomial's degree.
    :param bits: The bitstring to convert to a TS-hash polynomial modulo.
    :return: The TS-hash polynomial modulo corresponding to the bitstring.
    """
    return _POLY_RING.gen()**bits.len + bits_to_polynomial(bits)


def polynomial_modulo_to_bits(poly):
    """
    Converts a polynomial modulo to a bitstring.
    :param poly: The polynomial to convert.
    :return: The bitstring representation of the polynomial (MSB/highest exponent first).
    """
    poly_bits = polynomial_to_bits(poly - _POLY_RING.gen()**poly.degree())
    return extend_bits_to_width(poly_bits, poly.degree())


class TSHashParams(object):
    """
    Encapsulates the keys of a particular function from the TS-hash family.
    """
    def __init__(self, width, initial_value, polynomials_bits):
        self.width = width
        self.initial_value = self._canonize_initial_value(extend_bits_to_width(initial_value, self.width))

        assert len(polynomials_bits) == 2, 'Weird amount of polynomials'
        self.polynomials = tuple(extend_bits_to_width(poly, self.width) for poly in polynomials_bits)

        if not _SKIP_PRIMITIVITY_CHECK:
            for poly_bits in self.polynomials:
                poly_modulo = bits_to_polynomial_modulo(poly_bits)
                assert poly_modulo.is_primitive(), 'The feedback polynomials must be primitive'

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
    """
    Provides a both a streaming and a single-call interface to TS-hash calculations.
    """
    def __init__(self, tshash_params):
        self._params = tshash_params
        self._state = self._params.initial_value

    def update(self, data):
        """ Feed bits into the hash. """
        for d in data:
            self._state = self.calculate_new_state(self._params, self._state, d)

    def digest(self):
        """ Get the current digest. """
        return self._state

    def reset(self):
        """ Reset the state for a new hash computation. """
        self._state = self._params.initial_value

    def compute(self, data):
        """ Compute the hash of a whole bitstring. """
        self.reset()
        self.update(data)
        return self.digest()

    @classmethod
    def calculate_new_state(cls, tshash_params, current_state, bit):
        """ Calculate the state of TSHash given an intermediate state and the next bit fed into the function. """
        current_polynomial = tshash_params.polynomials[bit]
        shift_amount = 1 + current_state.find(_BITS[1])[0]
        new_state = (current_state << shift_amount) ^ current_polynomial
        return new_state


def mitm(tshash_params, end_states, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    """
    Perform a meet-in-the-middle attack trying to arrive at one of the desired end-states.
    :param tshash_params: The TSHash parameters.
    :param end_states: A dictionary of desired end states at which we want to arrive.
    :param except_bitstrings: Preimages to exclude.
    :param max_length: Maximum depth of BFS traversal across the graph.
    :return: A preimage, or None if no preimage was found.
    """

    empty = Bits()
    if tshash_params.initial_value in end_states and empty not in except_bitstrings:
        return empty

    # Starting conditions
    state_to_prefix = {tshash_params.initial_value: empty}
    state_to_suffix = {end_state: empty for end_state in end_states}
    advance_forward = True
    current_length = 0

    while current_length <= max_length:

        if advance_forward:
            # Advance the prefixes (forwards)
            new_state_to_prefix = {}
            for state, prefix in state_to_prefix.iteritems():
                for bit in _BITS:
                    new_state = TSHash.calculate_new_state(tshash_params, state, bit[0])
                    new_prefix = prefix + bit
                    new_state_to_prefix[new_state] = new_prefix

                    # Check whether we have an intersection
                    suffix = state_to_suffix.get(new_state)
                    if suffix is None:
                        continue
                    preimage = new_prefix + suffix
                    if preimage not in except_bitstrings:
                        return preimage
            state_to_prefix = new_state_to_prefix

        else:
            # Advance the suffixes (backwards)
            new_state_to_suffix = {}
            for state, suffix in state_to_suffix.iteritems():
                for bit in _BITS:
                    new_suffix = bit + suffix
                    polynomial = tshash_params.polynomials[bit[0]]

                    # Revert last generator multiplication
                    new_state = BitArray(bin=state.bin)  # Workaround for aliasing bug
                    new_state ^= polynomial
                    new_state >>= 1
                    new_state[0] = True
                    new_state >>= new_state.len - new_state.rfind(_BITS[1])[0] - 1
                    new_state = Bits(new_state)
                    assert TSHash.calculate_new_state(tshash_params, new_state, bit[0]) == state

                    new_state_to_suffix[new_state] = new_suffix

                    # Check whether we have an intersection
                    prefix = state_to_prefix.get(new_state)
                    if prefix is None:
                        continue
                    preimage = prefix + new_suffix
                    if preimage not in except_bitstrings:
                        return preimage

            state_to_suffix = new_state_to_suffix

        # Alternate between forward and backward
        advance_forward = not advance_forward
        current_length += 1

    return None


def mitm_state_preimage(tshash_params, state, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    """ Performs a meet-in-the-middle attack to find a preimage whose hash arrives at a certain state. """
    return mitm(tshash_params=tshash_params,
                end_states=(state, ),
                except_bitstrings=except_bitstrings,
                max_length=max_length)


def mitm_digest_preimage(tshash_params, digest, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    """ Performs a meet-in-the-middle attack to find a preimage whose hash arrives at a certain digest. """
    # We currently don't discard bits from the state to get a digest
    # possible_truncations = ('0b01', '0b11')
    possible_truncations = ('',)
    end_states = tuple(digest + possible_truncation for possible_truncation in possible_truncations)
    return mitm(tshash_params=tshash_params,
                end_states=end_states,
                except_bitstrings=except_bitstrings,
                max_length=max_length)


def mitm_second_preimage(tshash_params, bitstring, except_bitstrings=(), max_length=_MITM_DEFAULT_MAX_LENGTH):
    """ Performs a meet-in-the-middle attack to find a second preimage to the image of a given bitstring. """
    digest = TSHash(tshash_params).compute(bitstring)
    return mitm_digest_preimage(tshash_params=tshash_params,
                                digest=digest,
                                except_bitstrings=(bitstring,) + except_bitstrings,
                                max_length=max_length)


def get_state_to_preimages(tshash_params, depth=None):
    """
    Performs a BFS traversal of the TS-hash graph to yield a dictionary mapping
    states to all their preimages up to a certain length (depth).
    """
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
    """
    Calculates the trajectory of states traversed through in the TS-hash graph
    when performing a walk according to a particular bitstring.
    """
    tshash = TSHash(tshash_params)
    trajectory = [tshash._state]
    for bit in bitstring:
        tshash.update([bit])
        trajectory.append(tshash._state)
    return trajectory
