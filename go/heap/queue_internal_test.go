package heap

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func setup() Queue {
	q := NewQueue()

	q.Push(1)
	q.Push(2)
	q.Push(3)
	q.Pop()
	q.Push(4)
	q.Push(5)

	return q
}

func drain(q Queue) []uint64 {
	els := []uint64{}
	for {
		v, ok := q.Pop()
		if ok {
			els = append(els, v)
		} else {
			break
		}
	}
	return els
}

func TestEmptyBack(t *testing.T) {
	assert := assert.New(t)

	assert.Equal([]uint64{2, 3, 4, 5}, drain(setup()))

	q := setup()
	q.emptyBack()
	assert.Equal([]uint64{4, 5, 2, 3}, drain(q))
}
