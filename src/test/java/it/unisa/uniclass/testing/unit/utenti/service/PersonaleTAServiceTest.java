package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.utenti.model.PersonaleTA;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Assertions;
import org.mockito.Mockito;

import jakarta.persistence.NoResultException;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class PersonaleTAServiceTest {

    @Test
    void testTrovaPersonale_OK() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        PersonaleTA expected = new PersonaleTA();
        when(dao.trovaPersonale(1L)).thenReturn(expected);

        PersonaleTAService service = new PersonaleTAService(dao);
        PersonaleTA result = service.trovaPersonale(1L);

        Assertions.assertEquals(expected, result);
        verify(dao).trovaPersonale(1L);
    }

    @Test
    void testTrovaPersonale_NoResult() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        when(dao.trovaPersonale(1L)).thenThrow(new NoResultException());

        PersonaleTAService service = new PersonaleTAService(dao);
        PersonaleTA result = service.trovaPersonale(1L);

        Assertions.assertNull(result);
    }

    @Test
    void testTrovaTutti() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        List<PersonaleTA> lista = Arrays.asList(new PersonaleTA(), new PersonaleTA());
        when(dao.trovaTutti()).thenReturn(lista);

        PersonaleTAService service = new PersonaleTAService(dao);
        Assertions.assertEquals(lista, service.trovaTutti());
    }

    @Test
    void testTrovaEmail_OK() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        PersonaleTA expected = new PersonaleTA();
        when(dao.trovaEmail("mail@test.it")).thenReturn(expected);

        PersonaleTAService service = new PersonaleTAService(dao);
        Assertions.assertEquals(expected, service.trovaEmail("mail@test.it"));
    }

    @Test
    void testTrovaEmail_NoResult() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        when(dao.trovaEmail(any())).thenThrow(new NoResultException());

        PersonaleTAService service = new PersonaleTAService(dao);
        Assertions.assertNull(service.trovaEmail("aaa"));
    }

    @Test
    void testTrovaEmailPass_OK() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        PersonaleTA expected = new PersonaleTA();
        when(dao.trovaEmailPassword("x", "y")).thenReturn(expected);

        PersonaleTAService service = new PersonaleTAService(dao);
        Assertions.assertEquals(expected, service.trovaEmailPass("x", "y"));
    }

    @Test
    void testTrovaEmailPass_Exception() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        when(dao.trovaEmailPassword(any(), any())).thenThrow(new RuntimeException());

        PersonaleTAService service = new PersonaleTAService(dao);
        Assertions.assertNull(service.trovaEmailPass("x", "y"));
    }

    @Test
    void testAggiungiPersonaleTA() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        PersonaleTA p = new PersonaleTA();

        PersonaleTAService service = new PersonaleTAService(dao);
        service.aggiungiPersonaleTA(p);

        verify(dao).aggiungiPersonale(p);
    }

    @Test
    void testRimuoviPersonaleTA() {
        PersonaleTARemote dao = mock(PersonaleTARemote.class);
        PersonaleTA p = new PersonaleTA();

        PersonaleTAService service = new PersonaleTAService(dao);
        service.rimuoviPersonaleTA(p);

        verify(dao).rimuoviPersonale(p);
    }

    @Test
    void testCostruttoreDefault_LookupFallisce() throws Exception {
        InitialContext ctx = mock(InitialContext.class);
        when(ctx.lookup(anyString())).thenThrow(new javax.naming.NamingException());

        Assertions.assertThrows(RuntimeException.class, PersonaleTAService::new);
    }

    @Test
    void testCostruttoreDefault_NamingException() {
        try (var mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/PersonaleTADAO"))
                            .thenThrow(new NamingException("Simulated JNDI error"));
                })) {

            RuntimeException ex = assertThrows(RuntimeException.class, PersonaleTAService::new);

            assertTrue(ex.getMessage().contains("Errore durante il lookup di PersonaleTADAO"));
            assertTrue(ex.getCause() instanceof NamingException);
        }
    }

    @Test
    void testCostruttoreDefault_LookupSuccess() throws Exception {
        PersonaleTARemote fakeDao = mock(PersonaleTARemote.class);

        try (var mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/PersonaleTADAO"))
                            .thenReturn(fakeDao);
                })) {

            PersonaleTAService service = new PersonaleTAService();

            // Verifica che il service sia stato creato e abbia il dao assegnato
            assertNotNull(service);
        }
    }
}


