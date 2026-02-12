package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.service.CorsoService;
import it.unisa.uniclass.orari.service.dao.CorsoRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class CorsoServiceTest {

    @Mock
    private CorsoRemote corsoDao;

    @InjectMocks
    private CorsoService service;

    @Test
    @DisplayName("Trova Corso per ID: Successo e Catch NoResultException")
    void testTrovaCorso() {
        Corso c = new Corso();
        when(corsoDao.trovaCorso(1L)).thenReturn(c);
        assertSame(c, service.trovaCorso(1L));

        when(corsoDao.trovaCorso(2L)).thenThrow(new NoResultException());
        assertNull(service.trovaCorso(2L));
    }

    @Test
    @DisplayName("Test Metodi di Delega Semplice")
    void testDeleghi() {
        service.trovaCorsiCorsoLaurea("Informatica");
        verify(corsoDao).trovaCorsiCorsoLaurea("Informatica");

        service.trovaTutti();
        verify(corsoDao).trovaTutti();

        Corso c = new Corso();
        service.aggiungiCorso(c);
        verify(corsoDao).aggiungiCorso(c);

        service.rimuoviCorso(c);
        verify(corsoDao).rimuoviCorso(c);
    }
}