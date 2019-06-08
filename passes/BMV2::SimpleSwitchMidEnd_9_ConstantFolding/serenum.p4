--- before_pass
+++ after_pass
@@ -28,7 +28,7 @@ control c(inout Headers h) {
             if (h.eth.type == 16w0x800) 
                 h.eth.setInvalid();
             else 
-                h.eth.type = (bit<16>)16w0;
+                h.eth.type = 16w0;
     }
 }
 parser p<H>(packet_in _p, out H h);
