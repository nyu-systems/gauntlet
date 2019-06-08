--- before_pass
+++ after_pass
@@ -9,9 +9,9 @@ struct headers_t {
     data_h data;
 }
 parser MyP1(packet_in pkt, out headers_t hdr) {
-    headers_t hdr_1;
+    data_h hdr_1_data;
     state start {
-        hdr_1.data.setInvalid();
+        hdr_1_data.setInvalid();
         transition reject;
     }
 }
