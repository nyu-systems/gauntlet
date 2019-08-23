--- before_pass
+++ after_pass
@@ -26,7 +26,7 @@ parser parserI(packet_in pkt, out H hdr,
                 tmp.etherType = tmp_0[15:0];
             }
         }
-        transition select(tmp.etherType) {
+        transition select(tmp_0[15:0]) {
             16w0x1000 &&& 16w0x1000: accept;
         }
     }
