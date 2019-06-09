--- before_pass
+++ after_pass
@@ -91,6 +91,7 @@ parser ParserImpl(packet_in packet, out
     bit<8> Tcp_option_parser_n_sack_bytes;
     bit<8> Tcp_option_parser_tmp;
     Tcp_option_sack_top Tcp_option_parser_tmp_0;
+    bit<16> tmp;
     state start {
         packet.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -205,7 +206,10 @@ parser ParserImpl(packet_in packet, out
         transition Tcp_option_parser_next_option;
     }
     state Tcp_option_parser_parse_tcp_option_sack {
-        Tcp_option_parser_tmp_0 = packet.lookahead<Tcp_option_sack_top>();
+        {
+            tmp = packet.lookahead<bit<16>>();
+            Tcp_option_parser_tmp_0 = {tmp[15:8],tmp[7:0]};
+        }
         Tcp_option_parser_n_sack_bytes = Tcp_option_parser_tmp_0.length;
         verify(Tcp_option_parser_n_sack_bytes == 8w10 || Tcp_option_parser_n_sack_bytes == 8w18 || Tcp_option_parser_n_sack_bytes == 8w26 || Tcp_option_parser_n_sack_bytes == 8w34, error.TcpBadSackOptionLength);
         verify(Tcp_option_parser_tcp_hdr_bytes_left >= (bit<7>)Tcp_option_parser_n_sack_bytes, error.TcpOptionTooLongForHeader);
