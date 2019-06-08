--- before_pass
+++ after_pass
@@ -12,9 +12,6 @@ parser MyP1(packet_in pkt, out headers_t
     headers_t hdr_1;
     state start {
         hdr_1.data.setInvalid();
-        transition MyP2_start;
-    }
-    state MyP2_start {
         transition reject;
     }
 }
