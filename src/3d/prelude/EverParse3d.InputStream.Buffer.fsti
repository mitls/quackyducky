module EverParse3d.InputStream.Buffer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

open EverParse3d.InputStream

inline_for_extraction
noextract
val t : Type0

[@@ FStar.Tactics.Typeclasses.tcinstance]
noextract
inline_for_extraction
val inst : input_stream_inst t

val make
  (from: B.buffer U8.t)
  (n: U32.t)
: HST.ST t
  (requires (fun h -> B.live h from /\ U32.v n == B.length from))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer from) h h' /\
    footprint res `B.loc_includes` B.loc_buffer from /\
    (B.loc_unused_in h `B.loc_union` B.loc_buffer from) `B.loc_includes` footprint res /\
    live res h' /\
    get_remaining res h' == B.as_seq h from
  ))
