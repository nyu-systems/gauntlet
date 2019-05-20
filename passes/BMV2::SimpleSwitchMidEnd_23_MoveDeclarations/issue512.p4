*** dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-05-20 16:59:17.362156800 +0200
--- dumps/p4_16_samples/issue512.p4/pruned/issue512-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-05-20 16:59:17.364940500 +0200
*************** parser parserI(packet_in pkt, out Parsed
*** 26,38 ****
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      bool hasReturned_0;
      @name("cIngress.foo") action foo_0() {
          hasReturned_0 = false;
          meta.b = meta.b + 4w5;
          {
-             bool cond;
              {
-                 bool pred;
                  cond = meta.b > 4w10;
                  pred = cond;
                  {
--- 26,40 ----
  }
  control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
      bool hasReturned_0;
+     bool cond;
+     bool pred;
+     bool cond_0;
+     bool pred_0;
      @name("cIngress.foo") action foo_0() {
          hasReturned_0 = false;
          meta.b = meta.b + 4w5;
          {
              {
                  cond = meta.b > 4w10;
                  pred = cond;
                  {
*************** control cIngress(inout Parsed_packet hdr
*** 42,50 ****
              }
          }
          {
-             bool cond_0;
              {
-                 bool pred_0;
                  cond_0 = !hasReturned_0;
                  pred_0 = cond_0;
                  meta.b = (pred_0 ? meta.b + 4w5 : meta.b);
--- 44,50 ----
