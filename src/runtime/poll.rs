use arcstr::ArcStr;

use super::readback::Handle;
use crate::runtime::flat::runtime::Linker;

async fn poll_token_server(mut handle: Handle) {
    use futures::future::BoxFuture;
    use futures::stream::FuturesUnordered;
    use futures::stream::StreamExt as _;

    let mut clients: FuturesUnordered<BoxFuture<'static, crate::runtime::flat::readback::Handle>> =
        FuturesUnordered::new();

    loop {
        let op = handle.case().await;
        match op.as_str() {
            "#poll" => {
                // payload: (result_slot) next_slot
                // implemented as a Pair(left = next_slot, right = result_slot)
                let mut result_slot = handle.receive();

                if clients.is_empty() {
                    result_slot.signal(ArcStr::from("#empty"));
                    result_slot.break_();
                    continue;
                }

                let client = clients
                    .next()
                    .await
                    .expect("poll clients stream unexpectedly empty");

                result_slot.signal(ArcStr::from("#client"));
                result_slot.link(crate::runtime::Handle::from(client));
            }

            "#submit" => {
                // payload: (stream) next_slot
                // implemented as a Pair(left = next_slot, right = stream)
                let mut stream = handle.receive();

                loop {
                    let tag = stream.case().await;
                    match tag.as_str() {
                        "#end" => {
                            stream.continue_();
                            break;
                        }
                        "#item" => {
                            // payload: (client) tail
                            // implemented as a Pair(left = tail, right = client)
                            let client = stream.receive();
                            let client = client.handle;
                            clients.push(Box::pin(async move { client.await_ready().await }));
                        }
                        other => panic!("Invalid submit stream item: {other}"),
                    }
                }
            }

            "#close" => {
                // payload: !
                handle.erase();
                break;
            }

            other => panic!("Invalid poll token operation: {other}"),
        }
    }
}
