--- before_pass
+++ after_pass
@@ -25,31 +25,19 @@ parser parserI(packet_in pkt, out Parsed
     }
 }
 control cIngress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
-    bool hasReturned;
-    bool hasReturned_0;
-    bool cond;
-    bool pred;
-    bool cond_0;
-    bool pred_0;
     @name(".NoAction") action NoAction_0() {
     }
     @name("cIngress.foo") action foo(bit<16> bar) {
-        hasReturned = false;
         {
             {
-                cond = bar == 16w0xf00d;
-                pred = cond;
                 {
-                    hdr.ethernet.srcAddr = (pred ? 48w0xdeadbeeff00d : hdr.ethernet.srcAddr);
-                    hasReturned = (pred ? true : hasReturned);
+                    hdr.ethernet.srcAddr = (bar == 16w0xf00d ? 48w0xdeadbeeff00d : hdr.ethernet.srcAddr);
                 }
             }
         }
         {
             {
-                cond_0 = !hasReturned;
-                pred_0 = cond_0;
-                hdr.ethernet.srcAddr = (pred_0 ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
+                hdr.ethernet.srcAddr = (!(bar == 16w0xf00d ? true : false) ? 48w0x215241100ff2 : hdr.ethernet.srcAddr);
             }
         }
     }
@@ -63,9 +51,7 @@ control cIngress(inout Parsed_packet hdr
         default_action = NoAction_0();
     }
     apply {
-        hasReturned_0 = false;
         tbl1_0.apply();
-        hasReturned_0 = true;
     }
 }
 control cEgress(inout Parsed_packet hdr, inout mystruct1 meta, inout standard_metadata_t stdmeta) {
