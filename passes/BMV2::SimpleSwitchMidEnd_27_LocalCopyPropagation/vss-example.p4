--- before_pass
+++ after_pass
@@ -48,8 +48,6 @@ struct Parsed_packet {
 }
 parser TopParser(packet_in b, out Parsed_packet p) {
     bit<16> tmp;
-    bool tmp_0;
-    bool tmp_1;
     @name("TopParser.ck") Ck16() ck_0;
     state start {
         b.extract<Ethernet_h>(p.ethernet);
@@ -64,9 +62,7 @@ parser TopParser(packet_in b, out Parsed
         ck_0.clear();
         ck_0.update<Ipv4_h>(p.ip);
         tmp = ck_0.get();
-        tmp_0 = tmp == 16w0;
-        tmp_1 = tmp_0;
-        verify(tmp_1, error.IPv4ChecksumError);
+        verify(tmp == 16w0, error.IPv4ChecksumError);
         transition accept;
     }
 }
