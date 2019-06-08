--- dumps/pruned/issue420-BMV2::SimpleSwitchMidEnd_22_Predication.p4	2019-06-08 18:32:26.627551200 +0200
+++ dumps/pruned/issue420-BMV2::SimpleSwitchMidEnd_23_MoveDeclarations.p4	2019-06-08 18:32:26.629741600 +0200
@@ -27,14 +27,16 @@ parser parserI(packet_in pkt, out Parsed
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
     bool hasReturned_1;
     bool hasReturned_2;
+    bool cond;
+    bool pred;
+    bool cond_0;
+    bool pred_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo_0(bit<16> bar) {
         hasReturned_1 = false;
         {
-            bool cond;
             {
-                bool pred;
                 cond = bar == 16w0xf00d;
                 pred = cond;
                 {
@@ -44,9 +46,7 @@ control cIngress(inout Parsed_packet hdr
             }
         }
         {
-            bool cond_0;
             {
-                bool pred_0;
                 cond_0 = !hasReturned_1;
                 pred_0 = cond_0;
                 hdr.ethernet.srcAddr = (pred_0 ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
