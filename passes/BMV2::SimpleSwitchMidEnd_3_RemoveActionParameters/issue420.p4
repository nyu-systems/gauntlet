--- before_pass
+++ after_pass
@@ -25,10 +25,12 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
+    bool hasReturned_1;
+    bool hasReturned_2;
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo_0(bit<16> bar) {
-        bool hasReturned_1 = false;
+        hasReturned_1 = false;
         if (bar == 16w0xf00d) {
             hdr.ethernet.srcAddr = 48w0xdeadbeeff00d;
             hasReturned_1 = true;
@@ -46,7 +48,7 @@ control cIngress(inout Parsed_packet hdr
         default_action = NoAction_0();
     }
     apply {
-        bool hasReturned_2 = false;
+        hasReturned_2 = false;
         tbl1.apply();
         hasReturned_2 = true;
     }
