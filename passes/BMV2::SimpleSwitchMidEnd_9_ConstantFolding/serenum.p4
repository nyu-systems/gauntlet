--- dumps/pruned/serenum-BMV2::SimpleSwitchMidEnd_8_SimplifyKey.p4	2019-06-08 18:33:33.193166900 +0200
+++ dumps/pruned/serenum-BMV2::SimpleSwitchMidEnd_9_ConstantFolding.p4	2019-06-08 18:33:33.195714500 +0200
@@ -28,7 +28,7 @@ control c(inout Headers h) {
             if (h.eth.type == 16w0x800) 
                 h.eth.setInvalid();
             else 
-                h.eth.type = (bit<16>)16w0;
+                h.eth.type = 16w0;
     }
 }
 parser p<H>(packet_in _p, out H h);
