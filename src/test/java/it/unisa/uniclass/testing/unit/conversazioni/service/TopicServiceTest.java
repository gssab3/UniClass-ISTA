package it.unisa.uniclass.testing.unit.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.TopicService;
import it.unisa.uniclass.conversazioni.service.dao.TopicRemote;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test completi per TopicService senza JNDI.
 */
public class TopicServiceTest {

    @Mock
    private TopicRemote topicDao;

    private TopicService topicService;

    private Topic topic;
    private CorsoLaurea corsoLaurea;
    private Corso corso;

    @BeforeEach
    public void setUp() {
        MockitoAnnotations.openMocks(this);

        // Usa SOLO il costruttore con injection
        topicService = new TopicService(topicDao);

        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        corso = new Corso();
        corso.setNome("Programmazione Distribuita");
        corso.setCorsoLaurea(corsoLaurea);

        topic = new Topic();
        topic.setNome("Esame Finale");
        topic.setCorsoLaurea(corsoLaurea);
    }

    @Test
    public void testTrovaId() {
        when(topicDao.trovaId(1L)).thenReturn(topic);

        Topic result = topicService.trovaId(1L);

        assertNotNull(result);
        assertEquals(topic, result);
        verify(topicDao).trovaId(1L);
    }

    @Test
    public void testTrovaIdNoResultException() {
        when(topicDao.trovaId(999L)).thenThrow(new NoResultException());

        Topic result = topicService.trovaId(999L);

        assertNull(result);
        verify(topicDao).trovaId(999L);
    }

    @Test
    public void testTrovaNome() {
        when(topicDao.trovaNome("Esame Finale")).thenReturn(topic);

        Topic result = topicService.trovaNome("Esame Finale");

        assertNotNull(result);
        verify(topicDao).trovaNome("Esame Finale");
    }

    @Test
    public void testTrovaNomeNoResultException() {
        when(topicDao.trovaNome("Inesistente")).thenThrow(new NoResultException());

        Topic result = topicService.trovaNome("Inesistente");

        assertNull(result);
        verify(topicDao).trovaNome("Inesistente");
    }

    @Test
    public void testTrovaCorsoLaurea() {
        when(topicDao.trovaCorsoLaurea("Informatica")).thenReturn(topic);

        Topic result = topicService.trovaCorsoLaurea("Informatica");

        assertNotNull(result);
        verify(topicDao).trovaCorsoLaurea("Informatica");
    }

    @Test
    public void testTrovaCorso() {
        Topic t = new Topic();
        t.setNome("Lezione 1");
        t.setCorso(corso);

        when(topicDao.trovaCorso("Programmazione Distribuita")).thenReturn(t);

        Topic result = topicService.trovaCorso("Programmazione Distribuita");

        assertNotNull(result);
        assertNotNull(result.getCorso());
        verify(topicDao).trovaCorso("Programmazione Distribuita");
    }

    @Test
    public void testTrovaTutti() {
        List<Topic> topics = Arrays.asList(new Topic(), new Topic(), new Topic());
        when(topicDao.trovaTutti()).thenReturn(topics);

        List<Topic> result = topicService.trovaTutti();

        assertEquals(3, result.size());
        verify(topicDao).trovaTutti();
    }

    @Test
    public void testAggiungiTopic() {
        doNothing().when(topicDao).aggiungiTopic(topic);

        topicService.aggiungiTopic(topic);

        verify(topicDao).aggiungiTopic(topic);
    }

    @Test
    public void testRimuoviTopic() {
        doNothing().when(topicDao).rimuoviTopic(topic);

        topicService.rimuoviTopic(topic);

        verify(topicDao).rimuoviTopic(topic);
    }
}
