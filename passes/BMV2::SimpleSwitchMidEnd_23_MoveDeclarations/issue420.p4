*** dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:11.663711000 +0200
--- dumps/p4_16_samples/issue420.p4/pruned/issue420-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:11.667777800 +0200
*************** parser parserI(packet_in pkt, out Parsed
*** 27,40 ****
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      bool hasReturned_1;
      bool hasReturned_2;
      @name(".NoAction") action NoAction_0() {
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
          hasReturned_1 = false;
          {
-             bool cond;
              {
-                 bool pred;
                  cond = bar == 16w0xf00d;
                  pred = cond;
                  {
--- 27,42 ----
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      bool hasReturned_1;
      bool hasReturned_2;
+     bool cond;
+     bool pred;
+     bool cond_0;
+     bool pred_0;
      @name(".NoAction") action NoAction_0() {
      }
      @name("cIngress.foo") action foo_0(bit<16> bar) {
          hasReturned_1 = false;
          {
              {
                  cond = bar == 16w0xf00d;
                  pred = cond;
                  {
*************** control cIngress(inout Parsed_packet hdr
*** 44,52 ****
              }
          }
          {
-             bool cond_0;
              {
-                 bool pred_0;
                  cond_0 = !hasReturned_1;
                  pred_0 = cond_0;
                  hdr.ethernet.srcAddr = (pred_0 ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
--- 46,52 ----
