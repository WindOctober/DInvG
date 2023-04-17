#define MAX_FILE_SIZE 1000000
#define BUFFER_SIZE 8

typedef struct {
    unsigned char content[MAX_FILE_SIZE];
    unsigned int cur;
    unsigned int size;
    unsigned char buffer[BUFFER_SIZE];
    unsigned int buffer_len;
} File;

File file;

/*@ requires file.buffer_len < BUFFER_SIZE; 
    requires file.size == file.cur + file.buffer_len;
    ensures file.buffer_len < BUFFER_SIZE;
    ensures file.size == file.cur + file.buffer_len;
    ensures file.size == \old(file.size) + count;
    ensures memcmp(file.content + \old(file.cur), input, file.cur - old(file.cur)) == 0;
*/
void BufferWrite(unsigned char *input, unsigned int count)
{
    for (int i = 0; i < count; ++i) {
        file.buffer[file.buffer_len] = input[count];
        ++file.buffer_len;
        if (file.write_buffer_len == WRITE_BUFFER_SIZE) {
            memcpy(file.content + file.cur, file.buffer, BUFFER_SIZE);
            file.cur += file.buffer_len;
            file.buffer_len = 0;
        }
    }
    
    if (target->cur + target->write_buffer_len > target->size) {
        target->size = target->cur + target->write_buffer_len;
    }
}
