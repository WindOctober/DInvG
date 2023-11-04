extern void read_reset(int * reset);
extern void read_event(int * event);

/* Summary:
 *
 * [ reset0 = 0 and event0 = 0 ]
 * cnt = cnt0 and max = max0 and event0 = 0 and reset0 = 0
 * and event = 0 and reset = 0
 *
 * or
 *
 * [ reset0 = 0 and event0 >= 1 and cnt0 >= max0 ]
 * cnt = cnt0 and event = event0 and max = max0 and reset0 = 0
 * and reset = 0 and event >= 1 and cnt >= max
 *
 * or
 *
 * [ reset0 = 0 and cnt0 < max0 and event0 >= 1 ]
 * cnt = cnt0 + 1 and event = event0 and max = max0 and reset0 = 0
 * and reset = 0 and cnt <= max and event >= 1
 *
 * or
 *
 * [ reset0 = 0 and event0 <= -1 and cnt0 >= max0 ]
 * cnt = cnt0 and event = event0 and max = max0 and reset0 = 0
 * and reset = 0 and event <= -1 and cnt >= max
 *
 * or
 *
 * [ cnt0 < max0 and reset0 = 0 and event0 <= -1 ]
 * cnt = cnt0 + 1 and event = event0 and max = max0 and reset0 = 0
 * and reset = 0 and cnt <= max and event <= -1
 *
 * or
 *
 * [ reset0 >= 1 ]
 * reset = reset0 and event = event0 and max = max0 and cnt = 0
 * and reset >= 1
 *
 * or
 *
 * [ reset0 <= -1 ]
 * reset = reset0 and event = event0 and max = max0 and cnt = 0
 * and reset <= -1
 *
 */
void counter_step(int * cnt, int reset, int event, int max)
{
    if(reset)
    {
        *cnt = 0;
    }
    else if(event && *cnt < max)
    {
        *cnt = *cnt + 1;
    }
}

void counter_init(int * cnt)
{
    *cnt = 0;
}

void severt_meter(int max)
{
    int cnt1;
    int reset;
    int event;

    if(max < 0)
        return;

    counter_init(&cnt1);

    while(1)
    {
        /* invariant: cnt1 >= 0 and cnt1 <= max */

        read_reset(&reset);
        read_event(&event);

        counter_step(&cnt1, reset, event, max);
    }
}
