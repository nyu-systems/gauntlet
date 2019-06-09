--- before_pass
+++ after_pass
@@ -41,7 +41,10 @@ control MyID(packet_out buffer, out EMPT
     digest_t tmp;
     @name("MyID.digest") Digest<digest_t>() digest_0;
     apply {
-        tmp = {hdr.h,f.egress_port};
+        {
+            tmp.h = hdr.h;
+            tmp.port = f.egress_port;
+        }
         digest_0.pack(tmp);
     }
 }
