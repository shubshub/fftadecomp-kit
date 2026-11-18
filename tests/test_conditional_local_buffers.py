"""The opt-in contracts preserve frame bounds and expose their assumptions."""
import hashlib
from pathlib import Path
import hashlib
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import owner_admission_profile as owner

R0 = match.ARM_REG_R0
LOCAL = (False, False, True)
SAVED = (False, True, False)


def proof(policy, calls):
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.calls, result.observations = policy, calls, {}
    result.runtime_dependencies = []
    result.environment = {}
    result.owner_list_load = {}
    return result


def bound_output(calls, body, pinned):
    """Run the real OUTPUT bind_root with only ROM/index access stubbed."""
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.rom, result.entries = local.OUTPUT, b'', []
    result.mapping = result.index = b''
    result.dependencies, result.records, result.identities = {}, {}, {}
    result.span = lambda target: body
    with mock.patch.dict(local.DEPENDENCIES, {local.OUTPUT_CALLEE: pinned}), \
            mock.patch.object(local.named, 'validate_owner'), \
            mock.patch.object(local.graph, 'graph', return_value=({}, None, {}, dict(calls), {})), \
            mock.patch.object(owner, 'refine'), \
            mock.patch('known_query_native_closure_profile.environment_fingerprint', return_value={}):
        result.bind_root(b'', 0x08080EB8, calls)
    return result


FRAME = 'contiguous private frame from SP holding the complete aligned descriptor'
ADJACENT = 'exactly the descriptor and one adjacent nonempty payload'
POINTER = r'one descriptor\+4 word addressing the payload'
SCHEDULER_BODY, ALLOCATOR_BODY = bytes(range(60)), bytes(range(206))
PINNED = {0x08005B6C: (60, hashlib.sha256(SCHEDULER_BODY).hexdigest()),
          0x08005954: (206, hashlib.sha256(ALLOCATOR_BODY).hexdigest())}


def bound_scheduler(calls, bodies=None):
    """Run the real payload-scheduler bind_root with only ROM/index access stubbed."""
    bodies = {0x08005B6C: SCHEDULER_BODY, 0x08005954: ALLOCATOR_BODY, **(bodies or {})}
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.rom, result.entries = local.SCHEDULER_PAYLOAD, b'', []
    result.mapping = result.index = b''
    result.dependencies, result.records, result.identities = {}, {}, {}
    result.span = lambda target: bodies.get(target, b'\x00\x00')
    with mock.patch.dict(local.DEPENDENCIES, PINNED), \
            mock.patch.object(local.named, 'validate_owner'), \
            mock.patch.object(local.graph, 'graph', return_value=({}, None, {}, dict(calls), {})), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]), \
            mock.patch.object(owner, 'refine'), \
            mock.patch('known_query_native_closure_profile.environment_fingerprint', return_value={}):
        result.bind_root(b'', 0x080DF9AC, calls)
    return result


STATE_ROOTS = {  # genuine 60-byte roots; only the owner-list load at +28 differs
    0x0809A740: '10b583b0041c0a48026868460421a7f07dfd08486946019101aa5060606906492df0aefa6846007803b010bc02bc0847b8d43608b18b0908e9ab0908',
    0x0809A77C: '10b583b0041c0a48026868460421a7f05ffd08486946019101aa5060a06906492df090fa6846007803b010bc02bc0847b8d43608b18b0908e9ab0908'}
STATE_DEPENDENCIES = (0x080C7CC0, 0x0809ABE8, 0x080C7B74, 0x08098BB0)


def bound_state(address, data, policy=local.STATE):
    """Run the real state-iterator bind_root with only ROM/index access stubbed."""
    bodies = {target: bytes([n])*8 for n, target in enumerate(STATE_DEPENDENCIES)}
    initial, iterate = (16, 42) if policy == local.FLAGGED_STATE else (14, 32)
    calls = {address+initial: 0x0814224C, address+iterate: 0x080C7CC0}
    result = object.__new__(local.ConditionalLocalBufferProof)
    result.policy, result.rom, result.entries = policy, b'', []
    result.mapping = result.index = b''
    result.dependencies, result.records, result.identities = {}, {}, {}
    result.calls, result.observations, result.environment = {}, {}, {}
    result.span = lambda target: bodies.get(target, b'\x00\x00')
    pinned = {target: (8, hashlib.sha256(body).hexdigest()) for target, body in bodies.items()}
    with mock.patch.dict(local.DEPENDENCIES, pinned), \
            mock.patch.object(local.named, 'validate_owner'), \
            mock.patch.object(local.graph, 'graph', return_value=({}, None, {}, dict(calls), {})), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]), \
            mock.patch.object(owner, 'refine'), \
            mock.patch('known_query_native_closure_profile.environment_fingerprint', return_value={}):
        result.bind_root(data, address, calls)
    return result


class ConditionalLocalBufferTests(unittest.TestCase):
    def test_scheduler_accepts_complete_descriptor_and_preserved_alias(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        stack = [LOCAL]*7 + [SAVED]*4
        self.assertEqual(p.check_call(0x08005B6C, {R0+2: -44, R0+4: -44}, stack, site=100), {})
        manifest = p.contract_manifest()
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('ambient original R9', ' '.join(manifest['assumptions']))

    def test_scheduler_rejects_short_descriptor_and_saved_words(self):
        for offset in (-48, -40, -16, -4, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, {R0+2: offset}, [LOCAL]*7+[SAVED]*4, site=100)

    def test_scheduler_rejects_extra_argument_and_pointer_words(self):
        for aliases, slots in (({R0+2: -44, R0: -44}, None),
                               ({R0+2: -44}, {-40: -44})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, [LOCAL]*7+[SAVED]*4, slots, site=100)

    def test_scheduler_payload_root_records_both_pinned_dependencies(self):
        p = bound_scheduler({0x080DF9AC+40: 0x08005B6C})
        self.assertEqual(sorted(p.records), [0x08005954, 0x08005B6C])
        self.assertEqual(p.calls, {0x080DF9AC+40: 0x08005B6C})

    def test_scheduler_payload_root_refuses_guard_call_and_other_callees(self):
        # 0x08115AE4 shape: a guard call before the scheduler call.
        for calls in ({0x08115AE4+10: 0x080DD494, 0x08115AE4+34: 0x08005B6C},
                      {0x080DF9AC+40: 0x080DD494}, {}):
            with self.subTest(calls=calls), \
                    self.assertRaisesRegex(ValueError, 'one actual scheduler call'):
                bound_scheduler(calls)

    def test_scheduler_payload_root_refuses_wrong_dependency_body(self):
        for target, body in ((0x08005B6C, bytes(60)), (0x08005954, ALLOCATOR_BODY[:-2])):
            with self.subTest(target=hex(target)), \
                    self.assertRaisesRegex(ValueError, 'dependency identity differs'):
                bound_scheduler({0x080DF9AC+40: 0x08005B6C}, {target: body})

    def test_scheduler_payload_accepts_one_pointer_word_to_trailing_payload(self):
        # 0x080DF9AC: descriptor at sp, 12-byte payload at sp+0x1C, r4 keeps the payload.
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        stack = [LOCAL]*10 + [SAVED]*4
        self.assertEqual(p.check_call(0x08005B6C, {R0+2: -56, R0+4: -28}, stack,
                                      {-52: -28}, site=100), {})
        manifest = p.contract_manifest()
        observation = manifest['observations'][0]
        self.assertEqual((observation['payload_offset'], observation['payload_frame_bytes'],
                          observation['payload_extent']), (-28, 12, 'remaining-private-frame'))
        self.assertEqual(manifest['schema'], local.SCHEMAS[local.SCHEDULER_PAYLOAD])
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('premises, not proofs', ' '.join(manifest['assumptions']))
        self.assertIn('initialization is not checked', ' '.join(manifest['assumptions']))

    def test_scheduler_payload_records_sixteen_byte_extent(self):
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        p.check_call(0x08005B6C, {R0+2: -60}, [LOCAL]*11+[SAVED]*4, {-56: -32}, site=100)
        self.assertEqual(p.observations[100]['payload_frame_bytes'], 16)

    def test_scheduler_payload_accepts_payload_below_descriptor(self):
        # 0x080DE0AC: 12-byte payload at sp, descriptor at sp+0xC up to the saved words.
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        p.check_call(0x08005B6C, {R0+2: -44}, [LOCAL]*10+[SAVED]*4, {-40: -56}, site=100)
        self.assertEqual((p.observations[100]['payload_offset'], p.observations[100]['payload_frame_bytes']), (-56, 12))

    def test_scheduler_payload_rejects_descriptor_between_private_words(self):
        for aliases, slots in (({R0+2: -52}, {-48: -56}), ({R0+2: -52}, {-48: -24}),
                               ({R0+2: -48}, {-44: -56})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaisesRegex(ValueError, ADJACENT):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, [LOCAL]*10+[SAVED]*4, slots, site=100)

    def test_scheduler_payload_rejects_near_miss_pointer_words(self):
        stack = [LOCAL]*10 + [SAVED]*4
        cases = [(-56, slots) for slots in (None, {}, {-48: -28}, {-52: -32}, {-52: -56}, {-52: -12},
                                            {-52: -28, -48: -28}, {-52: -28, -24: -56})]
        cases += [(-44, {-40: -52}), (-44, {-40: -16})]  # payload below the descriptor
        for descriptor, slots in cases:
            with self.subTest(descriptor=descriptor, slots=slots), self.assertRaisesRegex(ValueError, POINTER):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, {R0+2: descriptor}, stack, slots, site=100)

    def test_scheduler_payload_rejects_other_frames_and_aliases(self):
        cases = (({R0+2: -56, R0: -28}, [LOCAL]*10+[SAVED]*4, {-52: -28}, 'additional register aliases'),
                 ({R0+2: -52}, [LOCAL]*10+[SAVED]*4, {-48: -24}, ADJACENT),         # descriptor inside the frame
                 ({R0+2: -44}, [LOCAL]*7+[SAVED]*4, {-40: -16}, ADJACENT),          # empty payload
                 ({R0+2: -56}, [LOCAL]*9+[SAVED]+[LOCAL]+[SAVED]*3, {-52: -28}, FRAME),  # saved word inside
                 ({R0+2: -56}, [LOCAL]*10+[SAVED]*4, {-52: -28, -36: -40}, POINTER),  # second pointer word
                 ({R0+2: -54}, [LOCAL]*10+[SAVED]*4, {-50: -26}, FRAME),            # unaligned descriptor
                 ({R0+2: -40}, [LOCAL]*10+[SAVED]*4, {-36: -56}, FRAME),            # descriptor overflows frame
                 ({R0+2: -16}, [SAVED]*4, {-12: -16}, FRAME),                       # no private words
                 ({R0+2: 4}, [LOCAL]*10+[SAVED]*4, {8: -56}, FRAME),                # positive offset
                 ({R0+2: -60}, [LOCAL]*10+[SAVED]*4+[LOCAL], {-56: -32}, FRAME))    # private word above saved
        for aliases, stack, slots, reason in cases:
            with self.subTest(aliases=aliases, slots=slots), self.assertRaisesRegex(ValueError, reason):
                proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C}).check_call(
                    0x08005B6C, aliases, stack, slots, site=100)

    def test_scheduler_payload_refuses_differing_frames_at_one_site(self):
        p = proof(local.SCHEDULER_PAYLOAD, {100: 0x08005B6C})
        p.check_call(0x08005B6C, {R0+2: -56}, [LOCAL]*10+[SAVED]*4, {-52: -28}, site=100)
        with self.assertRaisesRegex(ValueError, 'differs across incoming paths'):
            p.check_call(0x08005B6C, {R0+2: -60}, [LOCAL]*11+[SAVED]*4, {-56: -32}, site=100)

    def test_descriptor_only_scheduler_still_refuses_payload_word(self):
        with self.assertRaises(ValueError):
            proof(local.SCHEDULER, {100: 0x08005B6C}).check_call(
                0x08005B6C, {R0+2: -56}, [LOCAL]*10+[SAVED]*4, {-52: -28}, site=100)

    def test_state_clear_requires_constant_four_and_complete_local_word(self):
        p = proof(local.STATE, {100: 0x0814224C})
        self.assertEqual(p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                                     constants={R0+1: 4}, site=100), {})
        self.assertIn('not a proof', ' '.join(p.contract_manifest()['assumptions']))
        for constants in ({}, {R0+1: 8}):
            with self.subTest(constants=constants), self.assertRaises(ValueError):
                p.check_call(0x0814224C, {R0: -20}, [LOCAL]*3+[SAVED]*2,
                             constants=constants, site=100)

    def test_state_owner_list_load_accepts_aligned_offsets_and_binds_them(self):
        for address, offset in ((0x0809A740, 0x14), (0x0809A77C, 0x18)):
            with self.subTest(offset=hex(offset)):
                p = bound_state(address, bytes.fromhex(STATE_ROOTS[address]))
                self.assertEqual(p.owner_list_load, dict(site=address+28, base_register=4,
                                 destination_register=0, offset=offset, width=4))
                p.observations = {site: {} for site in p.calls}
                self.assertEqual(p.contract_manifest()['owner_list_load']['offset'], offset)

    def test_flagged_state_binds_update_and_list(self):
        # The two call fields are supplied through the decoded call map in this
        # bounded test. Native matching independently checks both displacements.
        body = bytes.fromhex('30b583b0051c0d486c46026868460421a7f040fd6178012008436070'
                             '08486946019101aa5060686906492df06dfa6846007803b030bc02bc'
                             '08470000b8d43608b18b0908e9ab0908')
        for address, list_load, flag, offset in ((0x0809A7B8, 0x68, 1, 20),
                                                  (0x0809A800, 0xA8, 1, 24),
                                                  (0x0809A848, 0xA8, 2, 24)):
            image = bytearray(body)
            image[22], image[38] = flag, list_load
            p = bound_state(address, bytes(image), local.FLAGGED_STATE)
            self.assertEqual(p.state_update, dict(load=address+20, store=address+26,
                             state_byte=1, operation='or', mask=flag, base_register=4))
            self.assertEqual(p.owner_list_load['offset'], offset)
        for offset, value in ((8, 0x68), (20, 0x21), (22, 4), (22, 2), (24, 0x48),
                              (26, 0x20), (32, 0x02), (38, 0x60), (58, 1), (64, 0xB3)):
            image = bytearray(body)
            image[offset] = value
            with self.subTest(offset=offset, value=value), self.assertRaisesRegex(ValueError, 'flagged state contract'):
                bound_state(0x0809A7B8, bytes(image), local.FLAGGED_STATE)
        with self.assertRaisesRegex(ValueError, 'state contract'):
            bound_state(0x0809A7B8, body)

    def test_flagged_state_requires_only_the_exact_live_state_alias(self):
        stack = [LOCAL]*3 + [SAVED]*3
        base = -24
        clear, walk = 0x0814224C, 0x080C7CC0
        p = proof(local.FLAGGED_STATE, {100: clear, 126: walk})
        args = {R0: base, R0+4: base}
        self.assertEqual(p.check_call(clear, args, stack, constants={R0+1: 4}, site=100), {})
        visitor = {R0+2: base+4, R0+4: base}
        slot = {base+4: base}
        self.assertEqual(p.check_call(walk, visitor, stack, slot, site=126), {})
        for aliases in ({R0: base}, {**args, R0+4: base+4}, {**args, R0+1: base}, {**args, R0+6: base}):
            with self.subTest(aliases=aliases), self.assertRaisesRegex(ValueError, 'actual local pointer'):
                p.check_call(clear, aliases, stack, constants={R0+1: 4}, site=100)
        for aliases, slots in (({R0+2: base+4}, slot), (visitor, {base+4: base+4}),
                               ({**visitor, R0: base}, slot)):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaisesRegex(ValueError, 'initialized state-pointer'):
                p.check_call(walk, aliases, stack, slots, site=126)
        with self.assertRaisesRegex(ValueError, 'pointer or return provenance'):
            p.check_indirect_target(clear, {R0+2: base}, {match.ARM_REG_LR}, site=100)

    def test_state_owner_list_load_refuses_other_registers_and_forms(self):
        # LDR R0,[R5,#0x18]; LDR R1,[R4,#0x18]; LDRH R0,[R4,#0x18]; LDR R0,[R4,R0].
        address = 0x0809A77C
        for value in (0x69A8, 0x69A1, 0x8B20, 0x5820):
            data = bytearray.fromhex(STATE_ROOTS[address])
            data[28:30] = value.to_bytes(2, 'little')
            with self.subTest(value=hex(value)), self.assertRaisesRegex(ValueError, 'exact four-byte state'):
                bound_state(address, bytes(data))

    def test_visitor_requires_exact_pointer_word(self):
        p = proof(local.STATE, {100: 0x080C7CC0})
        self.assertEqual(p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2,
                                     {-16: -20}, site=100), {})
        for slots in ({}, {-16: -12}, {-12: -20}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                p.check_call(0x080C7CC0, {R0+2: -16}, [LOCAL]*3+[SAVED]*2, slots, site=100)

    def test_output_word_accepts_single_local_result_word(self):
        p = proof(local.OUTPUT, {100: 0x080799C0})
        stack = [LOCAL] + [SAVED]*3
        self.assertEqual(p.check_call(0x080799C0, {R0+2: -16}, stack, site=100), {})
        self.assertEqual(p.check_call(0x080799C0, {R0+2: -16}, stack, site=100), {})
        manifest = p.contract_manifest()
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertIn('not alias-analysed', ' '.join(manifest['assumptions']))
        self.assertEqual(manifest['observations'][0]['bytes'], 4)
        self.assertEqual(manifest['observations'][0]['observed_store_bytes'], 2)

    def test_output_word_rejects_offsets_outside_its_local_word(self):
        for offset in (-20, -14, -12, -4, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                    0x080799C0, {R0+2: offset}, [LOCAL]+[SAVED]*3, site=100)
        # The alias and count checks pass here; only the local-word check refuses.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                0x080799C0, {R0+2: -16}, [SAVED, LOCAL, SAVED, SAVED], site=100)

    def test_output_word_rejects_extra_aliases_slots_and_wider_frames(self):
        for aliases, stack, slots in (({R0+2: -16, R0: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16, R0+1: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16, R0+4: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0: -16}, [LOCAL]+[SAVED]*3, None),
                                      ({R0+2: -16}, [LOCAL]+[SAVED]*3, {-16: -16}),
                                      ({R0+2: -20}, [LOCAL]*2+[SAVED]*3, None)):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                proof(local.OUTPUT, {100: 0x080799C0}).check_call(
                    0x080799C0, aliases, stack, slots, site=100)

    def test_output_word_rejects_other_targets_and_sites(self):
        p = proof(local.OUTPUT, {100: 0x080799C0})
        for address, site in ((0x0808CBDC, 100), (0x080799C0, 102)):
            with self.subTest(address=address, site=site), self.assertRaises(ValueError):
                p.check_call(address, {R0+2: -16}, [LOCAL]+[SAVED]*3, site=site)
        with self.assertRaises(ValueError):
            p.contract_manifest()
        with self.assertRaises(ValueError):
            p.check_indirect_target(local.thunk.ALIASES['_call_via_r2'], {}, (), site=100)

    def test_output_word_bind_root_accepts_one_pinned_callee(self):
        body = bytes(range(256))*6 + bytes(212)
        p = bound_output({100: 0x080799C0}, body, (1748, hashlib.sha256(body).hexdigest()))
        self.assertEqual(p.dependencies, {0x080799C0: body})
        self.assertEqual(p.records[0x080799C0]['bytes'], 1748)
        self.assertEqual(p.runtime_dependencies, [])

    def test_output_word_bind_root_rejects_call_shape(self):
        body = bytes(1748)
        pinned = (1748, hashlib.sha256(body).hexdigest())
        for calls in ({100: 0x080799C0, 120: 0x080799C0}, {100: 0x0808CBDC},
                      {100: 0x080799C0, 120: 0x0808CBDC}, {}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'one actual indexed output-word call'):
                bound_output(calls, body, pinned)

    def test_output_word_bind_root_rejects_callee_identity(self):
        body = bytes(range(256))*6 + bytes(212)
        flipped = bytearray(body)
        flipped[100] ^= 1
        short = body[:-2]
        for actual, pinned in ((bytes(flipped), (1748, hashlib.sha256(body).hexdigest())),
                               (short, (1748, hashlib.sha256(short).hexdigest()))):
            with self.subTest(size=len(actual)), self.assertRaisesRegex(ValueError, 'dependency identity differs'):
                bound_output({100: 0x080799C0}, actual, pinned)

    def test_unauthenticated_site_and_unobserved_call_refused(self):
        p = proof(local.SCHEDULER, {100: 0x08005B6C})
        with self.assertRaises(ValueError):
            p.check_call(0x08005B6C, {R0+2: -44}, [LOCAL]*7+[SAVED]*4, site=102)
        with self.assertRaises(ValueError):
            p.contract_manifest()

    def test_indirect_target_cannot_be_local_or_saved_return(self):
        p = proof(local.STATE, {100: 0x0814224C})
        p.check_indirect_target(0x0814224C, {R0: -20}, {match.ARM_REG_LR}, site=100)
        for aliases, returns in (({R0+2: -20}, ()), ({}, (R0+2,))):
            with self.subTest(aliases=aliases, returns=returns), self.assertRaises(ValueError):
                p.check_indirect_target(0x0814224C, aliases, returns, site=100)

    def test_profile_report_selection_is_explicit(self):
        for policy, schema in local.SCHEMAS.items():
            self.assertIn(policy, named.SELECTORS)
            self.assertEqual(owner.selector_for_report(f'* verification: `{schema}`'), policy)
        self.assertFalse(named.conditional_thunk_replay(None))

    def test_selectors_are_registered_with_dispatch_and_cli(self):
        # Registration is membership; the two tuples are not kept in one order.
        self.assertCountEqual(named.LOCAL_CALL_SELECTORS, local.SELECTORS)
        self.assertEqual(len(set(local.SELECTORS)), len(local.SELECTORS))
        source = (Path(match.__file__).read_text(encoding='utf-8'))
        line, = [row for row in source.splitlines() if '"--owner-runtime-profile", choices=(' in row]
        for policy in local.SELECTORS:
            self.assertIn(f'"{policy}"', line)


if __name__ == '__main__':
    unittest.main()
