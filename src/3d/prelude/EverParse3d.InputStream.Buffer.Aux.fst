module EverParse3d.InputStream.Buffer.Aux

(* This module is here to break circularity in KReMLin bundles (because Prims must be in the EverParse bundle because of the string type, as opposed to C,FStar,LowStar.) *)

module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

#set-options "--__temp_no_proj EverParse3d.InputStream.Buffer.Aux"

noeq
type input_buffer = {
  buf: B.buffer U8.t;
  len: U32.t;
  pos: B.pointer U32.t;
  g_all_buf: Ghost.erased (Seq.seq U8.t);
  g_all: Ghost.erased (Seq.seq U8.t);
  prf: squash (
    U32.v len <= B.length buf /\
    Seq.length g_all == U32.v len /\
    B.loc_disjoint (B.loc_buffer buf) (B.loc_buffer pos) /\
    Seq.length g_all_buf == B.length buf /\
    Ghost.reveal g_all == Seq.slice g_all_buf 0 (U32.v len)
  );
}
